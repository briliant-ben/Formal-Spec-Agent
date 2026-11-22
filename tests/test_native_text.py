"""Independent native UTF-8 transport, exact outcomes and transactional capacity."""
import copy
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from protocol_lab.ir import load
from protocol_lab.codegen import render,generate,TEXT_CAP,TEXT_POOL_CAP,Unsupported
from protocol_lab.codegen.execute import commands,build

EX=Path(__file__).resolve().parents[1]/'examples/lean-typed-efsm'


@unittest.skipUnless(shutil.which('cc'),'C99 compiler required')
class NativeTextTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp=tempfile.TemporaryDirectory();cls.root=Path(cls.tmp.name)
        cls.model=load(EX/'model.json')
        cls.cases=json.loads((EX/'cases.json').read_text())
        cls.exe=cls.compile(cls.model,'typed')

    @classmethod
    def tearDownClass(cls):cls.tmp.cleanup()

    @classmethod
    def compile(cls,model,name):
        source=cls.root/(name+'.c');exe=cls.root/name
        source.write_text(render(model))
        p=subprocess.run(['cc','-std=c99','-Wall','-Wextra','-Werror',str(source),'-o',str(exe)],
                         text=True,capture_output=True,timeout=60)
        if p.returncode:raise AssertionError(p.stdout+p.stderr)
        return exe

    def run_native(self,text,exe=None):
        p=subprocess.run([str(exe or self.exe)],input=text,text=True,capture_output=True,timeout=30)
        self.assertFalse(p.stderr)
        return p.returncode,[json.loads(line)for line in p.stdout.splitlines()]

    def dispatch(self,label,at=0):
        return 'D '+str(at)+' app.put b: 0 0 u:'+label.encode('utf8').hex()+' 1\n'

    def test_frozen_full_oracle_six_steps_one_process(self):
        steps=self.cases[0]['steps']
        text=commands(self.model,{'steps':[{k:v for k,v in s.items()if k in ('event','fields','at_ms')}for s in steps]})
        rc,rows=self.run_native(text);self.assertEqual(rc,0)
        actual=[dict(rule=r['transition'],event=r['event'],at_ms=r['time_ms'],
                     after=dict(r['after'],now_ms=r['time_ms']),emitted=r['emitted'])
                for r in rows if r['status']=='transition']
        self.assertEqual(actual,[t for s in steps for t in s['expected']['trace']])

    def test_unicode_nul_quotes_and_initial_override_are_full_values(self):
        label='A\0B 开😀\\"\r\n\t'
        text=commands(self.model,{'initial':{'label':label},'steps':[]})
        rc,rows=self.run_native(text);self.assertEqual(rc,0)
        self.assertEqual(rows[0]['snapshot']['variables']['label'],label)
        rc,rows=self.run_native('B\n'+self.dispatch(label))
        self.assertEqual(rc,0)
        self.assertEqual(rows[-1]['snapshot']['variables']['label'],label)
        self.assertEqual(rows[1]['emitted'][0]['fields']['label'],label)

    def test_utf8_byte_capacity_and_invalid_transport_rollback(self):
        boundary='😀'*(TEXT_CAP//4)
        rc,rows=self.run_native('B\n'+self.dispatch(boundary)+self.dispatch(boundary+'x',1)+self.dispatch('',2))
        self.assertEqual(rc,1)
        errors=[r for r in rows if r['status']=='error'];self.assertEqual(len(errors),1)
        self.assertEqual(errors[0]['failure'],'text_capacity')
        self.assertEqual(errors[0]['snapshot']['variables']['label'],boundary)
        self.assertEqual(rows[-1]['snapshot']['variables']['label'],'')
        # Odd/nonhex, overlong UTF8, surrogate, >10FFFF and truncated scalar.
        for raw in ['u:0','u:zz','u:c080','u:eda080','u:f4908080','u:e282']:
            with self.subTest(raw=raw):
                rc,rows=self.run_native('B\nD 0 app.put b: 0 0 '+raw+' 1\n'+self.dispatch('ok',1))
                self.assertEqual(rc,1)
                self.assertEqual(rows[1]['status'],'error')
                self.assertEqual(rows[1]['snapshot'],rows[0]['snapshot'])
                self.assertEqual(rows[-1]['snapshot']['variables']['label'],'ok')

    def test_full_pool_deduplicates_and_rejects_new_text_atomically(self):
        # Empty source literal occupies one entry. Full pool still admits repeats.
        text='B\n'+''.join(self.dispatch('label-'+str(i),i)for i in range(TEXT_POOL_CAP-1))
        text+=self.dispatch('overflow',64)+self.dispatch('label-0',65)+self.dispatch('',66)
        rc,rows=self.run_native(text);self.assertEqual(rc,1)
        errors=[r for r in rows if r['status']=='error'];self.assertEqual(len(errors),1)
        self.assertEqual(errors[0]['failure'],'text_capacity')
        self.assertEqual(errors[0]['snapshot']['variables']['label'],'label-62')
        from protocol_lab.pipeline.worker import native_class
        self.assertEqual(native_class('text_capacity'),'backend_domain_exceeded')
        self.assertEqual(rows[-1]['snapshot']['variables']['label'],'')

    def test_failed_command_rolls_back_pool_writes_state_and_outputs(self):
        model=copy.deepcopy(self.model)
        # Concrete invariant fault after interning and ordered writes.
        model['invariants'].append({'id':'TEST.NO.BAD','requirements':model['invariants'][0]['requirements'],
            'assert':{'op':'ne','args':[{'var':'label'},'bad']}})
        exe=self.compile(model,'rollback')
        # Every failing command first interns a fresh string then fails bool value
        # parsing. Those uncommitted strings must not consume the finite pool.
        errors=''.join('D 0 app.put b: 0 0 u:'+('discard-'+str(i)).encode().hex()+' 9\n'
                       for i in range(TEXT_POOL_CAP+5))
        rc,rows=self.run_native('B\n'+errors+self.dispatch('bad')+self.dispatch('valid',1),exe)
        self.assertEqual(rc,1)
        self.assertEqual(len([r for r in rows if r['status']=='error']),TEXT_POOL_CAP+6)
        self.assertEqual(len([r for r in rows if r['status']=='transition']),1)
        self.assertEqual(rows[-1]['snapshot']['variables']['label'],'valid')
        for row in rows:
            if row['status']=='error':self.assertEqual(row['snapshot'],rows[0]['snapshot'])

    def test_output_capacity_failure_discards_fresh_text_and_all_emissions(self):
        model=copy.deepcopy(self.model)
        emission=model['transitions'][0]['actions'][-1]
        model['transitions'][0]['actions'] += [copy.deepcopy(emission)for _ in range(40)]
        exe=self.compile(model,'output-rollback')
        rc,rows=self.run_native('B\n'+self.dispatch('x'*TEXT_CAP)+self.dispatch('ok',1),exe)
        self.assertEqual(rc,1)
        self.assertEqual(rows[1]['status'],'error')
        self.assertEqual(rows[1]['snapshot'],rows[0]['snapshot'])
        transitions=[r for r in rows if r['status']=='transition']
        self.assertEqual(len(transitions),1)
        self.assertEqual(transitions[0]['time_ms'],1)
        self.assertEqual(rows[-1]['snapshot']['variables']['label'],'ok')

    def test_source_literal_and_dynamic_text_have_identical_equality(self):
        model=copy.deepcopy(self.model)
        guard={'op':'and','args':[model['transitions'][0]['guard'],
               {'op':'eq','args':[{'event':'label'},'X\0开']}]}
        model['transitions'][0]['guard']=guard
        model['transitions'][1]['guard']={'op':'not','args':[guard]}
        exe=self.compile(model,'literal-equality')
        rc,rows=self.run_native('B\n'+self.dispatch('X\0开')+self.dispatch('X\0开Z',1),exe)
        self.assertEqual(rc,0)
        self.assertEqual([r['transition']for r in rows if r['status']=='transition'],['PUT.ACCEPT','PUT.REJECT'])

    def test_generation_binds_helper_and_real_compile(self):
        output=self.root/'generation';result=generate(EX/'model.json',output)
        self.assertEqual(result['backend'],'direct-c99-typed-text-v6')
        self.assertTrue(any(n.endswith('/text_runtime.c')for n in result['inputs']))
        self.assertTrue(any(n.endswith('/execute.py')for n in result['inputs']))
        self.assertEqual(result['limits']['text_entry_utf8_bytes'],TEXT_CAP)
        self.assertEqual(build(output,self.root/'build')['status'],'pass')

    def test_source_literal_outside_text_domain_is_explicitly_rejected(self):
        for label in ['x'*(TEXT_CAP+1),'\ud800']:
            model=copy.deepcopy(self.model);model['variables']['label']['initial']=label
            with self.assertRaises(Unsupported):render(model)
