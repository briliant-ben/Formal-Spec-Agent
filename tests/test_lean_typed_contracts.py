"""Generic typed before-filter contracts; definitions do not certify a model."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from formal_spec_agent import lean_backend as gate

ROOT = Path(__file__).resolve().parents[1]
EX = ROOT / 'examples/lean-typed-efsm'
LEAN = os.environ.get('FSA_LEAN') or shutil.which('lean')
MODULES = ['Foundation', 'ValueOps', 'TypedIR', 'TypedMachine', 'TypedContracts']
AUDITED = ['FormalSpecAgent.TypedContracts.candidate',
           'FormalSpecAgent.TypedContracts.runRule_eq_filter',
           'FormalSpecAgent.TypedContracts.preserving_rule_succeeds',
           'Controller.before_filter_property_rejects_bad_write',
           'Controller.coverage_only_declared_events']


class TypedContractTests(unittest.TestCase):
    def test_frozen_oracle_has_full_content_and_modular_boundary(self):
        self.assertEqual(hashlib.sha256((EX/'spec.md').read_bytes()).hexdigest(),
                         'c86a9a9144a6cdbb9cae939234c8fed2fe1023b8bf2fcda61219bc775e0c1a4c')
        self.assertEqual(hashlib.sha256((EX/'cases.json').read_bytes()).hexdigest(),
                         '2e6f5a87da2814e50488248590d64c927d913552afe9d81b4bde14ef3f054ace')
        steps = json.loads((EX/'cases.json').read_text())[0]['steps']
        self.assertEqual(len(steps), 6)
        self.assertEqual([s['expected']['after']['variables']['cursor'] for s in steps],
                         [0, 0, 0, 4294967295, 4294967295, 0])
        self.assertEqual(steps[1]['expected']['after']['variables']['buf'], [0,128,255,7])
        self.assertEqual(steps[4]['expected']['after']['variables']['buf'],
                         [0,255,1,254,2,253,3,252,4,251,5,250,6,249,7,248])
        self.assertEqual(steps[0]['expected']['after']['variables']['label'], '开\n\0')

    @unittest.skipUnless(LEAN, 'Pinned Lean required')
    def test_real_kernel_distinguishes_raw_preservation_from_runtime_filtering(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            env = dict(PATH=os.defpath, LEAN_PATH=str(root), LANG='C.UTF-8')
            def compile_module(name):
                return subprocess.run([LEAN, '-o', name+'.olean', name+'.lean'],
                    cwd=root, env=env, text=True, capture_output=True, timeout=60)
            for name in MODULES:
                shutil.copyfile(gate.HERE/('lean/'+name+'.lean'),root/(name+'.lean'))
                result=compile_module(name)
                self.assertEqual(result.returncode,0,name+'\n'+result.stdout+result.stderr)
            shutil.copyfile(ROOT/'tests/lean/TypedContractsAudit.lean',root/'Audit.lean')
            result=compile_module('Audit')
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            for name in AUDITED:
                self.assertLessEqual(set(gate.read_axioms(result.stdout,name)),gate.AXIOMS)
            # Restoring the original proposal's missing event-domain premise
            # makes the independent declared-event coverage contract fail.
            module=root/'TypedContracts.lean'
            text=module.read_text()
            self.assertEqual(text.count('    event ∈ model.externalEvents →\n'),1)
            module.write_text(text.replace('    event ∈ model.externalEvents →\n',''))
            result=compile_module('TypedContracts')
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            result=compile_module('Audit')
            self.assertNotEqual(result.returncode,0)
            self.assertIn('error:',result.stdout)


class TypedEfsmAdapterTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.workspace = self.root/'input'
        shutil.copytree(EX, self.workspace)
        self.task = self.workspace/'task.json'

    def tearDown(self):
        self.tmp.cleanup()

    def prepare(self, draft=False):
        return gate.prepare(self.task,self.workspace,gate.sha(self.task),draft=draft)

    def task_edit(self, change):
        task=json.loads(self.task.read_text()); change(task)
        self.task.write_text(json.dumps(task,indent=2)+'\n')

    def approve_model(self, change):
        model=self.workspace/'model.json'
        value=json.loads(model.read_text()); change(value)
        model.write_text(json.dumps(value,indent=2)+'\n')
        self.task_edit(lambda t:t.update(model_sha256=gate.sha(model)))
        source,_,_=self.prepare(draft=True)
        self.task_edit(lambda t:t.update(approved_sha256=hashlib.sha256(source.encode()).hexdigest()))

    def test_all_raw_rules_and_full_input_coverage_are_obligations(self):
        source,goals,inputs=self.prepare()
        self.assertEqual(set(goals),{'initial_valid','preserve_0','preserve_1',
            'guards_disjoint','coverage','context_valid_0','live_0','live_1',
            *('execution_0_'+str(i) for i in range(6))})
        self.assertIn('TypedContracts.RulePreserves model rule_0',source)
        self.assertIn('TypedContracts.Covers model [0]',source)
        self.assertIn('TypedMachine.rollback after_0_0 result_0_1',source)
        self.assertIn('tool/lean/TypedContracts.lean',inputs)
        self.assertNotIn('domainPredicate',source)

    def test_missing_or_duplicate_enabling_witness_is_rejected(self):
        self.task_edit(lambda t:t['witnesses'].pop())
        with self.assertRaisesRegex(ValueError,'Exactly one enabling'):
            self.prepare(draft=True)

    def test_model_source_and_approval_mutations_are_rejected(self):
        model=self.workspace/'model.json'; model.write_text(model.read_text()+' ')
        with self.assertRaisesRegex(ValueError,'pin differs'): self.prepare()

    def test_incomplete_oracle_is_rejected_even_with_reapproved_hash(self):
        cases=self.workspace/'cases.json'; data=json.loads(cases.read_text())
        del data[0]['steps'][0]['expected']['trace'][0]['event']['fields']['payload']
        cases.write_text(json.dumps(data))
        self.task_edit(lambda t:t.update(cases_sha256=gate.sha(cases)))
        with self.assertRaisesRegex(ValueError,'trace/after/input differs'):
            self.prepare(draft=True)

    @unittest.skipUnless(LEAN,'Pinned Lean required')
    def test_real_kernel_all_contracts_fresh_recheck_and_certificate_tampering(self):
        result=gate.check(self.task,self.workspace,self.root/'checked',
            self.workspace/'proofs.json',gate.sha(self.task),LEAN)
        self.assertEqual(result['status'],'checked_typed_efsm_contract')
        self.assertTrue(result['typed_efsm_contract_checked'])
        self.assertEqual(len(result['goals']),14)
        fresh=gate.verify(self.root/'checked',self.task,self.workspace,
            self.root/'fresh',gate.sha(self.task),LEAN)
        self.assertEqual(fresh['sources'],result['sources'])
        changed=dict(result,typed_efsm_contract_checked=False)
        (self.root/'checked/result.json').write_text(json.dumps(changed))
        with self.assertRaises(ValueError):
            gate.inspect_certificate(self.root/'checked',self.task,self.workspace,gate.sha(self.task))

    @unittest.skipUnless(LEAN,'Pinned Lean required')
    def test_same_length_wrong_bytes_fail_exact_contract_after_model_reapproval(self):
        def mutate(model):
            model['transitions'][0]['actions'][0]['set']['value']={'bytes':[7,255,128,0]}
        self.approve_model(mutate)
        result=gate.check(self.task,self.workspace,self.root/'wrong',
            self.workspace/'proofs.json',gate.sha(self.task),LEAN)
        self.assertEqual(result['status'],'fail')
        self.assertEqual(result['failed_module'],'Proofs')
