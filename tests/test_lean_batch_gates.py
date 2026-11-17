"""Batch runtime input isolation, approval epochs and real kernel replay bridge."""
import copy
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from formal_spec_agent import lean_backend as gate
from formal_spec_agent import lean_batch as batch
from formal_spec_agent import lean_batch_native as runtime
from formal_spec_agent import lean_machine_native as shared
from protocol_lab.ir import load

ROOT = Path(__file__).resolve().parents[1]
EX = ROOT / 'examples/lean-batch'
LEAN = os.environ.get('FSA_LEAN') or shutil.which('lean')


class BatchGateTests(unittest.TestCase):
    def test_runtime_builder_never_consumes_expected_state(self):
        cases = json.loads((EX / 'cases.json').read_text())
        view = batch.BatchView(load(EX / 'model.json'))
        source = runtime.render_runtime(view, shared.input_cases(cases))
        wrong = copy.deepcopy(cases)
        wrong[0]['steps'][0]['expected']['after']['now_ms'] = 999999
        self.assertEqual(source, runtime.render_runtime(view, shared.input_cases(wrong)))
        with self.assertRaises(ValueError):
            runtime.render_runtime(view, cases)
        self.assertNotIn('def witness_', source[0])
        self.assertNotIn('Approved', source[1])
        self.assertIn('BatchMachine.rollback', source[1])

    def test_trace_fields_and_failed_prefix_are_observed(self):
        cases = json.loads((EX / 'cases.json').read_text())
        view = batch.BatchView(load(EX / 'model.json'))
        rows = runtime.expected_values(view, cases)
        self.assertEqual(len(rows), 22)
        self.assertTrue(any(t['fields'] for r in rows for t in r['trace']))
        for row in rows:
            if row['status'] == 'error':
                self.assertEqual(row['trace'], [])
        mutated = copy.deepcopy(cases)
        step = mutated[0]['steps'][0]
        step['expected']['trace'][0]['event']['fields']['payload'] = [17]
        self.assertNotEqual(rows, runtime.expected_values(view, mutated))

    def test_input_mutation_during_render_is_rejected_before_execution(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            workspace = root / 'workspace'
            shutil.copytree(EX, workspace)
            model, cases = workspace / 'model.json', workspace / 'cases.json'
            original = runtime.render_runtime
            def mutate(view, inputs):
                rendered = original(view, inputs)
                cases.write_text(cases.read_text() + '\n')
                return rendered
            with patch.object(runtime, 'render_runtime', side_effect=mutate):
                with self.assertRaisesRegex(ValueError, 'changed during rendering'):
                    shared.run(model, workspace, cases, root / 'output',
                               gate.sha(model), gate.sha(cases), _profile='batch')
            self.assertFalse((root / 'output').exists())

    def test_batch_approval_pins_and_semantic_axiom_audit_are_strict(self):
        _, goals, inputs = gate.prepare(EX / 'task.json', EX, gate.sha(EX / 'task.json'))
        self.assertEqual(len(goals), 53)
        self.assertEqual(gate.contract_status(inputs), 'checked_batch_contract')
        self.assertIn('FormalSpecAgent.BatchReplay.sound', gate.semantic_audit_targets(inputs))
        for text in ['', "'subject' depends on axioms: [sorryAx]"]:
            with self.assertRaises(ValueError):
                gate.read_axioms(text, 'subject')
        self.assertEqual(gate.read_axioms("'subject' depends on axioms: [propext]", 'subject'), ['propext'])

    @unittest.skipUnless(LEAN, 'Pinned Lean required')
    def test_real_kernel_totality_replay_and_rejection_of_leaked_prefix(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            env = dict(PATH=os.defpath, LEAN_PATH=str(root), LANG='C.UTF-8')
            def compile_module(name):
                return subprocess.run([LEAN, '-o', name + '.olean', name + '.lean'],
                    cwd=root, env=env, text=True, capture_output=True, timeout=60)
            for name in batch.MODULES:
                shutil.copyfile(gate.HERE / ('lean/' + name + '.lean'), root / (name + '.lean'))
                result = compile_module(name)
                self.assertEqual(result.returncode, 0, name + '\n' + result.stdout + result.stderr)
            inputs = {'tool/lean/' + name + '.lean': gate.sha(root / (name + '.lean')) for name in batch.MODULES}
            targets = gate.semantic_audit_targets(inputs)
            (root / 'Audit.lean').write_text('import BatchReplay\n' + '\n'.join('#print axioms ' + name for name in targets))
            result = compile_module('Audit')
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            for name in targets:
                self.assertLessEqual(set(gate.read_axioms(result.stdout, name)), gate.AXIOMS)
            # The kernel must reject exposing an earlier success after the
            # later timer has failed; a genuine scheduler equation is required.
            (root / 'Leak.lean').write_text('''import BatchReplay
open FormalSpecAgent.TypedMachine FormalSpecAgent.BatchMachine FormalSpecAgent.BatchReplay
example (transition : Transition) (fault : Fault) :
    prepend transition (.error fault) =
      .ok { after := transition.after, trace := [transition] } := by rfl
''')
            result = compile_module('Leak')
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('error:', result.stdout)
