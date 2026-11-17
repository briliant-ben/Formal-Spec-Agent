"""Lean formal stage, complete source freezing and honest retained verdicts."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from formal_spec_agent import lean_backend as gate
from protocol_lab.pipeline.runner import run, verify
from protocol_lab.pipeline.task import load_task, inputs, sha

ROOT = Path(__file__).resolve().parents[1]
EX = ROOT/'examples/lean-efsm'
LEAN = os.environ.get('FSA_LEAN') or shutil.which('lean')


def write(path, value): path.write_text(json.dumps(value, indent=2)+'\n')


class LeanFlowTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(); self.root = Path(self.temp.name)
        self.w = self.root/'workspace'; shutil.copytree(EX, self.w)
        self.task = self.w/'flow.json'

    def tearDown(self): self.temp.cleanup()

    def test_v6_requires_pinned_Lean_inputs_and_same_subject(self):
        original = self.task.read_bytes()
        for field, value in [('strategy','initial-step-contracts'),('task_sha256','0'*64),('depth',1)]:
            t = json.loads(original); t['formal'][field] = value; write(self.task,t)
            with self.assertRaises(ValueError): load_task(self.task,self.w)
        t = json.loads(original); t['sources'] = [s for s in t['sources'] if s['path']!='proofs.json']; write(self.task,t)
        with self.assertRaisesRegex(ValueError,'source-pinned'): load_task(self.task,self.w)
        self.task.write_bytes(original)
        contract = json.loads((self.w/'task.json').read_text()); contract['model']='other.json'
        (self.w/'other.json').write_bytes((self.w/'model.json').read_bytes()); write(self.w/'task.json',contract)
        t = json.loads(original); t['formal']['task_sha256']=sha(self.w/'task.json'); write(self.task,t)
        with self.assertRaisesRegex(ValueError,'flow model itself'): load_task(self.task,self.w)

    def test_snapshot_covers_the_Lean_checker_and_semantics(self):
        t = load_task(self.task,self.w); frozen = inputs(self.task,self.w,t)
        for name in ['framework/lean_backend.py','framework/lean_efsm.py','framework/lean/EfsmSubset.lean','framework/lean/StateSubset.lean','framework/lean/lean-toolchain','workspace/task.json','workspace/proofs.json']:
            self.assertIn(name,frozen)

    @unittest.skipUnless(LEAN, 'Actual Lean required')
    def test_full_flow_and_readonly_verifier_reject_rebound_claims(self):
        out = self.root/'flow'
        with patch.dict(os.environ,{'FSA_LEAN':str(LEAN)}): report=run(self.task,self.w,out,sha(self.task))
        self.assertEqual(report['assessment'],'verified_event_slice')
        self.assertTrue(all(s['status']=='pass' for s in report['stages'].values()))
        self.assertEqual(report['stages']['formal']['data']['status'],'checked_efsm_contract')
        self.assertEqual(len(report['stages']['formal']['data']['goals']),25)
        self.assertEqual(len(report['stages']['tests']['data']['covered_rules']),6)
        self.assertFalse(report['protocol_correctness_proved'])
        # Retained audit reconstructs current trusted proof sources, but never
        # executes archived code, Lean, C or a solver.
        with patch('subprocess.run',side_effect=AssertionError('readonly audit executed a tool')):
            self.assertEqual(verify(out,self.w,sha(self.task))['status'],'retained_evidence_consistent')
        query=out/'stages/formal/queries/result.json'
        q=json.loads(query.read_text());q['c_expression_model_refinement_checked']=True;write(query,q)
        report['stages']['formal']['data']=q;write(out/'stages/formal/result.json',report['stages']['formal'])
        for p in [query,out/'stages/formal/result.json']: report['outputs'][str(p.relative_to(out))]=sha(p)
        write(out/'flow.json',report)
        with self.assertRaisesRegex(ValueError,'claim'): verify(out,self.w,sha(self.task))

    def test_missing_Lean_blocks_formal_without_fallback(self):
        out=self.root/'blocked'
        with patch.dict(os.environ,{'FSA_LEAN':str(self.root/'absent-lean')}): report=run(self.task,self.w,out,sha(self.task))
        self.assertEqual(report['assessment'],'blocked')
        self.assertEqual(report['stages']['formal']['status'],'blocked')
        self.assertEqual(report['stages']['formal']['classification'],'environment')
        self.assertEqual(report['stages']['compare']['status'],'pass')
        self.assertEqual(verify(out,self.w,sha(self.task))['assessment'],'blocked')

    @unittest.skipUnless(LEAN, 'Actual Lean version required for diagnostic')
    def test_resource_unknown_is_retained_and_never_promoted(self):
        task=self.w/'task.json';out=self.root/'timeout';original_run=subprocess.run
        def timeout_on_compile(command, **kwargs):
            if '-o' in command: raise subprocess.TimeoutExpired(command,60)
            return original_run(command,**kwargs)
        with patch('formal_spec_agent.lean_backend.subprocess.run',side_effect=timeout_on_compile):
            r=gate.check(task,self.w,out,self.w/'proofs.json',sha(task),LEAN)
        self.assertEqual(r['classification'],'resource_unknown')
        with self.assertRaises(ValueError): gate.inspect_certificate(out,task,self.w,sha(task))
        checked=gate.inspect_certificate(out,task,self.w,sha(task),require_pass=False)
        self.assertEqual(checked['status'],'fail');self.assertFalse(checked.get('efsm_contract_checked',False))
        r.update(status='checked_efsm_contract',efsm_contract_checked=True);write(out/'result.json',r)
        with self.assertRaises(ValueError): gate.inspect_certificate(out,task,self.w,sha(task))
