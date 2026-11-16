"""Real scoped state certificates, action order and invariant rollback."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from formal_spec_agent import lean_backend as gate
from protocol_lab.ir import load, Machine, ModelError
from protocol_lab.codegen import render
from protocol_lab.codegen.execute import commands

ROOT = Path(__file__).resolve().parents[1]
EX = ROOT/'examples/lean-state'
LEAN = os.environ.get('FSA_LEAN') or shutil.which('lean')


def write(p, v): p.write_text(json.dumps(v, indent=2) + '\n')


class StateTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(); self.root = Path(self.temp.name)
        self.w = self.root/'workspace'; shutil.copytree(EX, self.w)
        self.task = self.w/'task.json'

    def tearDown(self): self.temp.cleanup()

    def prepare(self, draft=False):
        return gate.prepare(self.task, self.w, gate.sha(self.task), draft=draft)

    def rebind(self):
        t = json.loads(self.task.read_text()); t['model_sha256'] = gate.sha(self.w/'model.json'); write(self.task, t)
        source, _, _ = self.prepare(True)
        t['approved_sha256'] = hashlib.sha256(source.encode()).hexdigest(); write(self.task, t)

    def test_frozen_state_view_and_claim_are_distinct_from_C_proof(self):
        source, goals, inputs = self.prepare()
        self.assertEqual(len(goals), 11)
        self.assertIn('StateSubset.execute', source)
        self.assertIn('tool/lean/StateSubset.lean', inputs)
        self.assertNotIn('tool/lean/CSubset.lean', inputs)
        self.assertIn('Not guard selection', gate.unit_scope(inputs))

    def test_reference_checks_order_and_discards_writes_emits_trace_on_failure(self):
        m = load(self.w/'model.json'); t = json.loads(self.task.read_text())
        for w in t['witnesses']:
            machine = Machine(m, dict(zip(m['variables'], w['initial'])))
            before = machine.snapshot()
            try: machine.dispatch('update', {'value': w['fields'][0]}, 0)
            except ModelError:
                self.assertFalse(w['accepted']); self.assertEqual(machine.snapshot(), before); self.assertEqual(machine.trace, [])
            else:
                self.assertTrue(w['accepted'])
                self.assertEqual([r['fields']['value'] for r in machine.trace[0]['emitted']], [row[1] for row in w['emitted']])
            self.assertEqual(list(machine.values.values()), w['values'])

    def test_unpinned_model_spec_adapter_and_semantics_refused(self):
        old = self.task.read_bytes()
        for k in ['model_sha256', 'adapter_sha256', 'state_semantics_sha256', 'approved_sha256']:
            t = json.loads(old); t[k] = '0'*64; write(self.task, t)
            with self.assertRaises(ValueError): self.prepare()
        self.task.write_bytes(old); (self.w/'spec.md').write_text('changed')
        with self.assertRaisesRegex(ValueError, 'source digest'): self.prepare()

    def test_unsupported_arithmetic_timers_and_guard_selection_refused(self):
        old = (self.w/'model.json').read_bytes()
        for which in ['arithmetic', 'timer', 'guard']:
            m = json.loads(old)
            if which == 'arithmetic': m['transitions'][0]['actions'][0]['set']['value'] = {'op':'add', 'args':[1, 2]}
            if which == 'timer': m['timers'] = {'r':{'event':'update'}}
            if which == 'guard': m['transitions'][0]['guard'] = False
            write(self.w/'model.json', m)
            t = json.loads(self.task.read_text()); t['model_sha256'] = gate.sha(self.w/'model.json'); write(self.task, t)
            with self.assertRaises(ValueError): self.prepare(True)

    def test_nonvacuity_requires_both_outcomes(self):
        t = json.loads(self.task.read_text())
        for w in t['witnesses']: w['accepted'] = False
        write(self.task, t)
        with self.assertRaisesRegex(ValueError, 'Both successful'): self.prepare(True)

    @unittest.skipUnless(shutil.which('cc'), 'C99 compiler required')
    def test_independent_native_order_and_rollback_on_frozen_literals(self):
        m = load(self.w/'model.json'); c = self.root/'subject.c'; exe = self.root/'subject'
        c.write_text(render(m))
        subprocess.run(['cc', '-std=c99', '-Wall', '-Wextra', '-Werror', str(c), '-o', str(exe)], check=True, capture_output=True)
        for w in json.loads(self.task.read_text())['witnesses']:
            scenario = dict(initial=dict(zip(m['variables'], w['initial'])), steps=[dict(at_ms=0,event='update',fields={'value':w['fields'][0]})])
            p = subprocess.run([str(exe)], input=commands(m, scenario), capture_output=True, text=True, timeout=10)
            rows = [json.loads(line) for line in p.stdout.splitlines()]
            self.assertEqual(p.returncode, 0 if w['accepted'] else 1)
            self.assertEqual(list(rows[-1]['snapshot']['variables'].values()), w['values'])
            transitions = [r for r in rows if r['status'] == 'transition']
            self.assertEqual(len(transitions), int(w['accepted']))
            if transitions: self.assertEqual([e['fields']['value'] for e in transitions[0]['emitted']], [e[1] for e in w['emitted']])
            else: self.assertEqual(rows[-1]['snapshot'], rows[0]['snapshot'])

    @unittest.skipUnless(LEAN, 'Actual Lean required')
    def test_actual_state_certificate_and_fresh_recheck(self):
        r = gate.check(self.task, self.w, self.root/'check', self.w/'proofs.json', gate.sha(self.task), LEAN)
        self.assertEqual(r['status'], 'checked_state_contract')
        self.assertTrue(r['state_action_contract_checked']); self.assertFalse(r['c_expression_model_refinement_checked'])
        fresh = gate.verify(self.root/'check', self.task, self.w, self.root/'recheck', gate.sha(self.task), LEAN)
        self.assertEqual(fresh['status'], 'checked_state_contract')
        original = (self.root/'check/result.json').read_bytes()
        for key, value in [('status','checked_expression_contract'),('c_expression_model_refinement_checked',True),('compiler_correctness_proved',True),('scope','whole protocol')]:
            wrong = json.loads(original); wrong[key] = value; write(self.root/'check/result.json',wrong)
            with self.assertRaisesRegex(ValueError, 'claim'):
                gate.verify(self.root/'check', self.task, self.w, self.root/'forged', gate.sha(self.task), LEAN)
        (self.root/'check/result.json').write_bytes(original)

    @unittest.skipUnless(LEAN, 'Actual Lean required')
    def test_rebound_action_order_mutant_fails_frozen_expected_values(self):
        m = json.loads((self.w/'model.json').read_text())
        m['transitions'][0]['actions'][0:2] = list(reversed(m['transitions'][0]['actions'][0:2]))
        write(self.w/'model.json', m); self.rebind()
        r = gate.check(self.task, self.w, self.root/'mutant', self.w/'proofs.json', gate.sha(self.task), LEAN)
        self.assertEqual(r['status'], 'fail'); self.assertEqual(r['classification'], 'proof_failure')

    @unittest.skipUnless(LEAN, 'Actual Lean required')
    def test_rebound_false_rollback_or_contradictory_admission_is_rejected(self):
        old = self.task.read_bytes()
        t = json.loads(old); t['witnesses'][1]['values'] = [-1,-1]; write(self.task, t); self.rebind()
        r = gate.check(self.task, self.w, self.root/'wrong-rollback', self.w/'proofs.json', gate.sha(self.task), LEAN)
        self.assertEqual(r['classification'], 'proof_failure')
        self.task.write_bytes(old)
        m = json.loads((self.w/'model.json').read_text()); m['invariants'][0]['assert'] = False
        write(self.w/'model.json', m); self.rebind()
        r = gate.check(self.task, self.w, self.root/'vacuous', self.w/'proofs.json', gate.sha(self.task), LEAN)
        self.assertEqual(r['classification'], 'proof_failure')
