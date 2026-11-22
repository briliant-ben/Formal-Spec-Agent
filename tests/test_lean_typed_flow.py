"""Typed all-rule Lean contracts integrated with every deterministic flow stage."""
import json
import os
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

from protocol_lab.pipeline.runner import run,verify
from protocol_lab.pipeline.task import load_task,inputs,sha

ROOT=Path(__file__).resolve().parents[1]
EX=ROOT/'examples/lean-typed-efsm'
LEAN=os.environ.get('FSA_LEAN')or shutil.which('lean')


class TypedFlowTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.root=Path(self.tmp.name)
        self.workspace=self.root/'input';shutil.copytree(EX,self.workspace)
        self.task=self.workspace/'flow.json'

    def tearDown(self):self.tmp.cleanup()

    def test_explicit_versions_do_not_alias_scalar_and_typed_contracts(self):
        original=self.task.read_bytes()
        for version,strategy in [('spec-flow-task-v6','lean-typed-efsm'),('spec-flow-task-v7','lean-efsm')]:
            value=json.loads(original);value['schema']=version;value['formal']['strategy']=strategy
            self.task.write_text(json.dumps(value))
            with self.assertRaisesRegex(ValueError,'strategy'):load_task(self.task,self.workspace)
        value=json.loads(original);value['formal']['depth']=1;self.task.write_text(json.dumps(value))
        with self.assertRaises(ValueError):load_task(self.task,self.workspace)

    def test_every_contract_source_and_framework_module_is_frozen(self):
        value=load_task(self.task,self.workspace);frozen=inputs(self.task,self.workspace,value)
        self.assertIn('framework/lean_typed_efsm.py',frozen)
        self.assertIn('framework/lean/TypedContracts.lean',frozen)
        self.assertIn('tool/codegen/text_runtime.c',frozen)
        value['sources']=[s for s in value['sources']if s['path']!='cases.json']
        self.task.write_text(json.dumps(value))
        with self.assertRaisesRegex(ValueError,'Every Lean contract'):load_task(self.task,self.workspace)

    def test_seed_is_exact_frozen_projection_not_regenerated_runtime_expected(self):
        cases=json.loads((self.workspace/'cases.json').read_text())[0]['steps']
        seed=json.loads((self.workspace/'seed.json').read_text())
        self.assertEqual(len(seed['steps']),len(cases))
        for old,new in zip(cases,seed['steps']):
            for name in ('event','fields','at_ms'):self.assertEqual(new[name],old[name])
            self.assertEqual(new['expect_trace'],[{k:t[k]for k in ('at_ms','emitted')}for t in old['expected']['trace']])
        self.assertEqual(seed['expect'],{k:v for k,v in cases[-1]['expected']['after'].items()if k!='now_ms'})

    @unittest.skipUnless(LEAN,'Actual Lean required')
    def test_actual_ten_stages_and_readonly_audit_reject_rebound_claim(self):
        out=self.root/'flow'
        with patch.dict(os.environ,{'FSA_LEAN':str(LEAN)}):report=run(self.task,self.workspace,out,sha(self.task))
        self.assertEqual(report['assessment'],'verified_event_slice')
        self.assertTrue(all(s['status']=='pass'for s in report['stages'].values()))
        self.assertEqual(report['stages']['formal']['data']['status'],'checked_typed_efsm_contract')
        self.assertEqual(len(report['stages']['formal']['data']['goals']),14)
        self.assertEqual(report['stages']['tests']['data']['covered_rules'],['PUT.ACCEPT','PUT.REJECT'])
        self.assertEqual(report['stages']['reference']['data']['trace_contract_steps_checked'],6)
        self.assertFalse(report['protocol_correctness_proved'])
        with patch('subprocess.run',side_effect=AssertionError('readonly checker ran a tool')):
            self.assertEqual(verify(out,self.workspace,sha(self.task))['status'],'retained_evidence_consistent')
        # A rebound flag with updated outer hashes still cannot claim a scalar proof.
        query=out/'stages/formal/queries/result.json'
        data=json.loads(query.read_text());data['typed_efsm_contract_checked']=False
        query.write_text(json.dumps(data));report['stages']['formal']['data']=data
        stage=out/'stages/formal/result.json';stage.write_text(json.dumps(report['stages']['formal']))
        for p in [query,stage]:report['outputs'][str(p.relative_to(out))]=sha(p)
        (out/'flow.json').write_text(json.dumps(report))
        with self.assertRaisesRegex(ValueError,'claim'):verify(out,self.workspace,sha(self.task))

    def test_missing_Lean_blocks_only_formal_and_never_falls_back(self):
        out=self.root/'blocked'
        with patch.dict(os.environ,{'FSA_LEAN':str(self.root/'absent-lean')}):report=run(self.task,self.workspace,out,sha(self.task))
        self.assertEqual(report['assessment'],'blocked')
        self.assertEqual(report['stages']['formal']['status'],'blocked')
        self.assertEqual(report['stages']['compare']['status'],'pass')
        self.assertEqual(verify(out,self.workspace,sha(self.task))['assessment'],'blocked')
