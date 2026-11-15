"""Frozen contract, anti-cheat and actual optional Lean-kernel checks."""
import copy
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from formal_spec_agent import lean_backend as backend
from protocol_lab.ir import load, Machine
from protocol_lab.codegen import render
from protocol_lab.codegen.execute import commands

ROOT=Path(__file__).resolve().parents[1]
EXAMPLE=ROOT/'examples/lean-bytes'
LEAN=os.environ.get('FSA_LEAN')or shutil.which('lean')
if os.environ.get('FSA_LEAN_REQUIRED')=='1' and not LEAN:
    raise RuntimeError('This CI gate requires the pinned Lean checker; no silent skip')


def write(p,v): p.write_text(json.dumps(v,indent=2)+'\n')


class LeanInputTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.base=Path(self.temp.name)
        self.workspace=self.base/'workspace';shutil.copytree(EXAMPLE,self.workspace)
        self.task=self.workspace/'task.json'
    def tearDown(self): self.temp.cleanup()
    def prepare(self): return backend.prepare(self.task,self.workspace,backend.sha(self.task))
    def mutate(self,fn):
        t=json.loads(self.task.read_text());fn(t);write(self.task,t)
    def approve_model_mutation(self,fn):
        p=self.workspace/'model.json';m=json.loads(p.read_text());fn(m);write(p,m)
        self.mutate(lambda t:t.update(model_sha256=backend.sha(p)))
        source,_,_=backend.prepare(self.task,self.workspace,backend.sha(self.task),draft=True)
        self.mutate(lambda t:t.update(approved_sha256=hashlib.sha256(source.encode()).hexdigest()))

    def test_actual_IR_expression_is_lowered_and_frozen(self):
        source,goals,_=self.prepare()
        self.assertIn('FormalSpecAgent.byteSlice f0 f1 f2',source)
        self.assertEqual(len(goals),9)
        self.assertIn('witness_valid',goals)
        self.assertEqual(hashlib.sha256(source.encode()).hexdigest(),json.loads(self.task.read_text())['approved_sha256'])

    def test_wrong_digest_changed_model_sources_and_semantics_reject(self):
        with self.assertRaisesRegex(ValueError,'digest'):backend.prepare(self.task,self.workspace,'0'*64)
        for field in ['model_sha256','foundation_sha256','approved_sha256']:
            with self.subTest(field=field):
                old=self.task.read_bytes();self.mutate(lambda t:t.update({field:'0'*64}))
                with self.assertRaises(ValueError):self.prepare()
                self.task.write_bytes(old)
        (self.workspace/'spec.md').write_text('weakened contract')
        with self.assertRaisesRegex(ValueError,'Specification digest'):self.prepare()

    def test_unsupported_operators_are_refused_not_skipped(self):
        self.approve_model_mutation(lambda m:None)
        p=self.workspace/'model.json';m=json.loads(p.read_text());m['transitions'][0]['actions'][0]['set']['value']=dict(op='add',args=[1,2]);write(p,m)
        self.mutate(lambda t:t.update(model_sha256=backend.sha(p)))
        with self.assertRaisesRegex(ValueError,'Unsupported Lean operator'):self.prepare()

    def test_proof_data_cannot_declare_axioms_change_statements_or_execute_commands(self):
        for data in [[{'sorry':True}],[{'exact':'sorry'}],[{'exact':'True.intro\naxiom bad : False'}],[{'exact':'native_decide'}],[{'run_tac':True}],[{'exact':'IO.println "pass"'}],[{'simp':['Approved.expression; exact sorry']}],[{'split':[[],[]]}]]:
            with self.subTest(data=data):
                with self.assertRaises(ValueError):backend.proof_lines(data)

    def test_positive_witnesses_and_complete_obligations_required(self):
        self.mutate(lambda t:[w.update(expected=0)for w in t['witnesses']])
        with self.assertRaisesRegex(ValueError,'nonzero'):self.prepare()
        shutil.copyfile(EXAMPLE/'task.json',self.task)
        p=self.base/'missing.json';write(p,{})
        with self.assertRaisesRegex(ValueError,'Every frozen obligation'):
            backend.check(self.task,self.workspace,self.base/'out',p,backend.sha(self.task),'missing-lean')

    def test_missing_Lean_is_blocked_not_proved(self):
        r=backend.check(self.task,self.workspace,self.base/'out',self.workspace/'proofs.json',backend.sha(self.task),'no-such-lean-checker-fsa')
        self.assertEqual(r['status'],'blocked');self.assertNotIn('axioms',r)
        self.assertFalse(r['protocol_correctness_proved'])

    def test_extended_model_dependencies_must_be_pinned(self):
        overlay=self.workspace/'overlay.json'
        write(overlay,dict(ir_version='0.5',extends='model.json'))
        self.mutate(lambda t:t.update(model='overlay.json',model_sha256=backend.sha(overlay)))
        with self.assertRaisesRegex(ValueError,'Every extended model base'):self.prepare()
        self.mutate(lambda t:t['sources'].append(dict(path='model.json',sha256=backend.sha(self.workspace/'model.json'))))
        self.prepare()
        m=json.loads((self.workspace/'model.json').read_text());m['scope']['excluded'].append('unapproved modification')
        write(self.workspace/'model.json',m)
        with self.assertRaisesRegex(ValueError,'Specification digest'):self.prepare()

    def test_wallclock_timeout_never_counts_as_proof(self):
        with patch.object(backend.shutil,'which',return_value='/usr/bin/false'), patch.object(backend.subprocess,'check_output',return_value='Lean (version 4.35.0, test)'), patch.object(backend.subprocess,'run',side_effect=subprocess.TimeoutExpired(['lean'],60)):
            r=backend.check(self.task,self.workspace,self.base/'timeout',self.workspace/'proofs.json',backend.sha(self.task),'lean')
        self.assertEqual(r['status'],'fail');self.assertEqual(r['classification'],'resource_unknown')
        self.assertNotIn('axioms',r)

    @unittest.skipUnless(shutil.which('cc'),'C99 compiler required')
    def test_independent_literals_match_reference_and_actual_generated_C(self):
        m=load(self.workspace/'model.json');witnesses=json.loads(self.task.read_text())['witnesses']
        scenario=dict(steps=[dict(at_ms=0,event='inspect',fields=w['fields'])for w in witnesses])
        c=self.base/'protocol.c';c.write_text(render(m));exe=self.base/'native'
        subprocess.run(['cc','-std=c99','-Wall','-Wextra','-Werror',str(c),'-o',str(exe)],check=True,capture_output=True)
        p=subprocess.run([str(exe)],input=commands(m,scenario),text=True,capture_output=True,timeout=15)
        self.assertEqual(p.returncode,0,p.stdout+p.stderr)
        native=[r for r in map(json.loads,p.stdout.splitlines())if r['status']=='transition']
        reference=Machine(m)
        for w,row in zip(witnesses,native):
            reference.dispatch('inspect',w['fields'],0)
            expected=[dict(message='observed',fields=dict(value=w['expected']))]
            self.assertEqual(row['emitted'],expected)
            self.assertEqual(reference.trace[-1]['emitted'],expected)
        self.assertEqual(len(native),len(witnesses))


@unittest.skipUnless(LEAN,'Optional pinned Lean checker unavailable; dedicated CI requires it')
class LeanKernelTests(unittest.TestCase):
    setUp=LeanInputTests.setUp
    tearDown=LeanInputTests.tearDown
    prepare=LeanInputTests.prepare
    mutate=LeanInputTests.mutate
    approve_model_mutation=LeanInputTests.approve_model_mutation
    def check(self,proofs=None,out='checked'):
        return backend.check(self.task,self.workspace,self.base/out,proofs or self.workspace/'proofs.json',backend.sha(self.task),LEAN)

    def test_all_contracts_checked_and_fresh_recheck_ignores_archived_code(self):
        r=self.check();self.assertEqual(r['status'],'checked_expression_contract')
        self.assertEqual(len(r['axioms']),9)
        self.assertTrue(all(set(a)<=backend.AXIOMS for a in r['axioms'].values()))
        fresh=backend.verify(self.base/'checked',self.task,self.workspace,self.base/'fresh',backend.sha(self.task),LEAN)
        self.assertEqual(fresh['status'],'checked_expression_contract')
        self.assertEqual(fresh['sources'],r['sources'])
        self.assertFalse(fresh['compiler_correctness_proved'])
        # Tampering a retained log is caught before rebuilding any proof.
        (self.base/'checked'/'Audit.stdout').write_text('forged')
        with self.assertRaisesRegex(ValueError,'Retained evidence changed'):
            backend.verify(self.base/'checked',self.task,self.workspace,self.base/'bad',backend.sha(self.task),LEAN)

    def test_always_zero_IR_mutant_fails_nonzero_witness(self):
        self.approve_model_mutation(lambda m:m['transitions'][0]['actions'][0]['set'].update(value=0))
        r=self.check();self.assertEqual(r['status'],'fail');self.assertEqual(r['failed_module'],'Proofs')

    def test_source_changed_during_kernel_check_is_invalidated(self):
        actual_run=backend.subprocess.run
        def mutate_after_audit(command,**kwargs):
            completed=actual_run(command,**kwargs)
            if command[-1]=='Audit.lean':(self.workspace/'spec.md').write_text('changed during checking')
            return completed
        with patch.object(backend.subprocess,'run',side_effect=mutate_after_audit):r=self.check()
        self.assertEqual(r['status'],'invalidated_inputs')

    def test_internal_sorry_axiom_cannot_bypass_kernel_audit(self):
        # This term can be accepted by Lean with sorryAx; our separate fresh
        # audit must reject it even though Lean returns successful elaboration.
        source,goals,_=self.prepare();p=self.base/'axiom.json'
        write(p,{n:[dict(exact='sorryAx _ true')]for n in goals})
        with self.assertRaisesRegex(ValueError,'Unapproved proof axioms'):
            self.check(p)
