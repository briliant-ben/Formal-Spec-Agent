"""Actual Lean EFSM-contract certificates and frozen evidence independence."""
import hashlib
import json
import os
import re
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from formal_spec_agent import lean_backend as gate
from protocol_lab.ir import load
from protocol_lab.codegen import render
from protocol_lab.codegen.execute import commands
from protocol_lab.flow import run_scenario, TraceContractMismatch

ROOT = Path(__file__).resolve().parents[1]
EX = ROOT / 'examples/lean-efsm'
LEAN = os.environ.get('FSA_LEAN') or shutil.which('lean')


def write(p, v):
    p.write_text(json.dumps(v, indent=2) + '\n')


class EfsmTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.w = self.root / 'workspace'
        shutil.copytree(EX, self.w)
        self.task = self.w / 'task.json'

    def tearDown(self):
        self.temp.cleanup()

    def prepare(self, draft=False):
        return gate.prepare(self.task, self.w, gate.sha(self.task), draft=draft)

    def rebind(self, mutate_model=False):
        """Regenerate approved source hash after any model/spec change."""
        if mutate_model:
            # model.json is already modified by the caller; update its hash in task
            t = json.loads(self.task.read_text())
            t['model_sha256'] = gate.sha(self.w / 'model.json')
            write(self.task, t)
        source, _, _ = self.prepare(True)
        t = json.loads(self.task.read_text())
        t['approved_sha256'] = hashlib.sha256(source.encode()).hexdigest()
        write(self.task, t)

    def test_prepare_generates_25_obligations_and_efsm_scope(self):
        source, goals, inputs = self.prepare()
        self.assertEqual(len(goals), 25)
        self.assertEqual(goals,
                         ['initial_valid',
                          'preserve_0', 'preserve_1', 'preserve_2', 'preserve_3',
                          'preserve_4', 'preserve_5',
                          'overlap_0_1', 'overlap_2_3',
                          'cover_0_0', 'cover_0_1', 'cover_1_0', 'cover_1_1',
                          'live_0', 'live_1', 'live_2', 'live_3', 'live_4', 'live_5',
                          'witness_0', 'witness_1', 'witness_2', 'witness_3',
                          'witness_4', 'witness_5'])
        self.assertIn('tool/lean/EfsmSubset.lean', inputs)
        self.assertNotIn('tool/lean/CSubset.lean', inputs)
        self.assertIn('Not C refinement', gate.unit_scope(inputs))
        self.assertIn('def rules', source)
        self.assertIn('∀ (v0 : Int) (f0 : Int)', source)
        self.assertNotIn('StateSubset.execute', source)  # No invariant filtering premise.

    def test_prepare_refuses_unpinned_spec_model_or_approved_hash(self):
        old = self.task.read_bytes()
        for key in ['adapter_sha256', 'model_sha256', 'approved_sha256']:
            t = json.loads(old)
            t[key] = '0' * 64
            write(self.task, t)
            with self.assertRaises(ValueError):
                self.prepare()
        self.task.write_bytes(old)
        (self.w / 'spec.md').write_text('changed')
        with self.assertRaisesRegex(ValueError, 'digest'):
            self.prepare()

    def test_prepare_refuses_unsupported_features(self):
        old_model = (self.w / 'model.json').read_bytes()
        for mutation in ['timers', 'bytes', 'unknown_guard']:
            m = json.loads(old_model)
            if mutation == 'timers':
                m['timers'] = {'r': {'event': 'put'}}
            if mutation == 'bytes':
                m['events']['put']['fields']['value'] = 'bytes'
            if mutation == 'unknown_guard':
                m['transitions'][0]['guard'] = {'op': 'unknown_op', 'args': []}
            write(self.w / 'model.json', m)
            t = json.loads(self.task.read_text())
            t['model_sha256'] = gate.sha(self.w / 'model.json')
            write(self.task, t)
            with self.assertRaises(ValueError):
                self.prepare(True)

    def test_reference_literal_oracle_accepts_frozen_seed_and_detects_output_mutant(self):
        m = load(self.w / 'model.json')
        seed = json.loads((self.w / 'seed.json').read_text())
        machine = run_scenario(m, seed)
        expected = json.loads((self.w / 'seed.json').read_text())['expect']
        self.assertEqual(machine.state, expected['state'])
        self.assertEqual(machine.values, expected['variables'])
        self.assertEqual([msg for step in machine.trace for msg in step['emitted']],
                         [msg for step in seed['steps'] for msg in step['expect_trace'][0]['emitted']])

        # Mutate model: on TAKE_FULL emit delivered with wrong value (slot+1) while state/slot unchanged.
        m2 = json.loads((self.w / 'model.json').read_text())
        for tr in m2['transitions']:
            if tr['id'] == 'TAKE_FULL':
                tr['actions'][0]['emit']['fields']['value'] = {'op': 'add', 'args': [{'var': 'slot'}, 1]}
        write(self.w / 'model_mutant.json', m2)
        seed2 = json.loads((self.w / 'seed.json').read_text())
        with self.assertRaises(TraceContractMismatch):
            run_scenario(m2, seed2)

    @unittest.skipUnless(shutil.which('cc'), 'C99 compiler required')
    def test_generated_c_executes_frozen_seed_exactly(self):
        m = load(self.w / 'model.json')
        c_file = self.root / 'subject.c'
        exe = self.root / 'subject'
        c_file.write_text(render(m))
        subprocess.run(['cc', '-std=c99', '-Wall', '-Wextra', '-Werror', str(c_file), '-o', str(exe)],
                       check=True, capture_output=True)
        seed = json.loads((self.w / 'seed.json').read_text())
        p = subprocess.run([str(exe)], input=commands(m, seed), capture_output=True, text=True, timeout=10)
        rows = [json.loads(line) for line in p.stdout.splitlines()]
        self.assertEqual(p.returncode, 0)
        transitions = [r for r in rows if r['status'] == 'transition']
        self.assertEqual(len(transitions), 6)
        emitted = []
        for r in transitions:
            emitted.extend(e['fields']['value'] for e in r['emitted'])
        self.assertEqual(emitted, [0, 65, 255, 256, 255, 0])
        self.assertEqual(rows[-1]['snapshot']['variables']['slot'], 0)

    @unittest.skipUnless(LEAN, 'Actual Lean required')
    def test_actual_efsm_certificate_and_fresh_recheck(self):
        r = gate.check(self.task, self.w, self.root / 'check', self.w / 'proofs.json',
                       gate.sha(self.task), LEAN)
        self.assertEqual(r['status'], 'checked_efsm_contract')
        self.assertTrue(r['efsm_contract_checked'])
        self.assertFalse(r['c_expression_model_refinement_checked'])
        self.assertFalse(r['compiler_correctness_proved'])
        self.assertFalse(r['protocol_correctness_proved'])
        fresh = gate.verify(self.root / 'check', self.task, self.w, self.root / 'recheck',
                            gate.sha(self.task), LEAN)
        self.assertEqual(fresh['status'], 'checked_efsm_contract')

        original = (self.root / 'check/result.json').read_bytes()
        for key, value in [('status', 'checked_expression_contract'),
                           ('efsm_contract_checked', False),
                           ('c_expression_model_refinement_checked', True),
                           ('compiler_correctness_proved', True),
                           ('scope', 'whole protocol')]:
            wrong = json.loads(original)
            wrong[key] = value
            write(self.root / 'check/result.json', wrong)
            with self.assertRaisesRegex(ValueError, 'claim'):
                gate.verify(self.root / 'check', self.task, self.w, self.root / 'forged',
                            gate.sha(self.task), LEAN)
        (self.root / 'check/result.json').write_bytes(original)

    @unittest.skipUnless(LEAN, 'Actual Lean required')
    def test_invariant_preservation_prevents_illegal_write_even_if_rollback_may_hide(self):
        # Mutate PUT_EMPTY (first put transition) to set slot=999, but still keep state FULL.
        # The invariant says FULL requires 1<=slot<=255, so preservation must fail.
        m = json.loads((self.w / 'model.json').read_text())
        for tr in m['transitions']:
            if tr['id'] == 'PUT_EMPTY':
                tr['actions'][0]['set']['value'] = 999
        write(self.w / 'model.json', m)
        self.rebind(mutate_model=True)
        r = gate.check(self.task, self.w, self.root / 'illegal-write', self.w / 'proofs.json',
                       gate.sha(self.task), LEAN)
        self.assertEqual(r['classification'], 'proof_failure')

    @unittest.skipUnless(LEAN, 'Actual Lean required')
    def test_conflicting_rule_mutation_fails_overlap_goal(self):
        # Change guard of REJECT_EMPTY to True, so it overlaps with PUT_EMPTY for valid values.
        m = json.loads((self.w / 'model.json').read_text())
        for tr in m['transitions']:
            if tr['id'] == 'REJECT_EMPTY':
                tr['guard'] = True
        write(self.w / 'model.json', m)
        self.rebind(mutate_model=True)
        r = gate.check(self.task, self.w, self.root / 'overlap-conflict', self.w / 'proofs.json',
                       gate.sha(self.task), LEAN)
        self.assertEqual(r['classification'], 'proof_failure')

    @unittest.skipUnless(LEAN, 'Actual Lean required')
    def test_false_invariant_admission_is_rejected_by_initial_or_preservation(self):
        # Make invariant false and see proof fail.
        m = json.loads((self.w / 'model.json').read_text())
        m['invariants'][0]['assert'] = False
        write(self.w / 'model.json', m)
        self.rebind(mutate_model=True)
        r = gate.check(self.task, self.w, self.root / 'false-invariant', self.w / 'proofs.json',
                       gate.sha(self.task), LEAN)
        self.assertEqual(r['classification'], 'proof_failure')

    @unittest.skipUnless(LEAN, 'Actual Lean required')
    def test_deleted_rule_fails_actual_missing_group_coverage(self):
        m = json.loads((self.w/'model.json').read_text())
        m['transitions'] = [r for r in m['transitions'] if r['id'] != 'TAKE_EMPTY']
        write(self.w/'model.json', m)
        t = json.loads(self.task.read_text())
        t['witnesses'] = [w for w in t['witnesses'] if w['rule'] != 'TAKE_EMPTY']
        write(self.task, t); self.rebind(mutate_model=True)
        source, goals, _ = self.prepare()
        self.assertIn('cover_0_1', goals)
        self.assertIn('covered [] 0', source)
        # Supply all remaining proofs, so this reaches the actual false coverage
        # obligation rather than failing on missing/renumbered proof names.
        ns = 'FormalSpecAgent.EfsmSubset.'; st = 'FormalSpecAgent.StateSubset.'
        definitions = ['Approved.invariants'] + ['Approved.rule_'+str(i) for i in range(len(m['transitions']))] + [ns+'invariantsHold', ns+'guardHolds', ns+'evalPredicate', ns+'covered', st+'work', st+'evalInteger']
        proofs = {}
        for goal in goals:
            start = [{'unfold':['Approved.'+goal]}]
            if goal == 'initial_valid' or goal.startswith(('live_', 'witness_')):
                proofs[goal] = start + [{'decide':True}]; continue
            if goal.startswith(('preserve_', 'overlap_')):
                event = m['transitions'][int(goal.split('_')[1])]['event']
            else: event = list(m['events'])[int(goal.split('_')[2])]
            binders = ['v0'] + (['f0'] if event == 'put' else []) + ['Hinv'] + (['Hguard'] if goal.startswith('preserve_') else [])
            proofs[goal] = start + [{'intro':binders}, {'simp_all':definitions}, {'all_goals':[{'omega':True}]}]
        write(self.w/'mutant-proofs.json', proofs)
        out = self.root/'missing-coverage'
        result = gate.check(self.task, self.w, out, self.w/'mutant-proofs.json', gate.sha(self.task), LEAN)
        self.assertEqual(result['classification'], 'proof_failure')
        lines = (out/'Proofs.lean').read_text().splitlines()
        first = next(i+1 for i,s in enumerate(lines) if s.startswith('theorem cover_0_1 '))
        following = next(i+1 for i,s in enumerate(lines) if i+1 > first and s.startswith('theorem '))
        errors = [int(n) for n in re.findall(r'Proofs.lean:(\d+):\d+: error:', (out/'Proofs.stdout').read_text())]
        self.assertTrue(errors)
        self.assertTrue(all(first <= n < following for n in errors), errors)

    @unittest.skipUnless(LEAN, 'Actual Lean required')
    def test_witness_values_are_checked_against_transition_results(self):
        # Change witness for PUT_EMPTY to expect stored value 66 instead of 65.
        t = json.loads(self.task.read_text())
        for w in t['witnesses']:
            if w['rule'] == 'PUT_EMPTY':
                w['after']['emitted'][0]['fields']['value'] = 66
        write(self.task, t)
        self.rebind(mutate_model=False)
        r = gate.check(self.task, self.w, self.root / 'wrong-witness', self.w / 'proofs.json',
                       gate.sha(self.task), LEAN)
        self.assertEqual(r['classification'], 'proof_failure')
