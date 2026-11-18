"""Independent frozen deadline, refresh, full-content and rollback observations."""
import copy
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from protocol_lab.ir import load,Machine,ModelError
from protocol_lab.codegen import render
from protocol_lab.codegen.execute import commands
from protocol_lab.json_values import same_value

ROOT=Path(__file__).resolve().parents[1]
EX=ROOT/'examples/lean-timed-efsm'


def observe_reference(model,case):
    machine=Machine(model);operations=[]
    for step in case['steps']:
        start=len(machine.trace);error=None
        try:
            if step['kind']=='tick':machine.tick(step['at_ms'])
            else:machine.dispatch(step['event'],step['fields'],step['at_ms'])
        except ModelError as fault:error=str(fault)
        trace=[dict(rule=r['transition'],event=r['event'],at_ms=r['time_ms'],
                    after=dict(r['after'],now_ms=r['time_ms']),emitted=r['emitted'])
               for r in machine.trace[start:]]
        outcome=dict(status='error'if error else'ok',after=dict(machine.snapshot(),now_ms=machine.now_ms),trace=trace)
        if error:outcome['fault']='time'if error=='Time must be monotonic integer milliseconds'else'other_model_error'
        operations.append(outcome)
    return operations


class TimedCellTests(unittest.TestCase):
    def setUp(self):
        self.model=load(EX/'model.json')
        self.case=json.loads((EX/'cases.json').read_text())[0]
        self.expected=[s['expected']for s in self.case['steps']]

    def test_frozen_oracle_and_reference_complete_operations(self):
        self.assertEqual(hashlib.sha256((EX/'cases.json').read_bytes()).hexdigest(),
                         '3eefe8ccf5ddaf5940fbf92d3f45ec1caf7b6d605e0c7cd5809851d4f06a9888')
        self.assertTrue(same_value(observe_reference(self.model,self.case),self.expected))
        self.assertEqual([r['rule']for r in self.expected[2]['trace']],['EXPIRY.HOT','PUT.ACCEPT.COLD'])
        self.assertEqual(self.expected[7]['trace'],[])
        self.assertEqual(self.expected[-1]['after'],self.expected[-2]['after'])

    def test_reject_refresh_fault_preserves_invariants_but_violates_oracle(self):
        model=copy.deepcopy(self.model)
        rule=next(r for r in model['transitions']if r['id']=='PUT.REJECT.HOT')
        rule['actions'].insert(-1,{'arm':{'timer':'expiry','delay_ms':10}})
        # This valid IR action leaves HOT/active and every data invariant true.
        # Its wrong deadline and later missing expiry are independently observable.
        observed=observe_reference(model,self.case)
        self.assertEqual(observed[1]['status'],'ok')
        self.assertEqual(observed[1]['after']['timers'],{'expiry':15})
        self.assertNotEqual(observed,self.expected)

    @unittest.skipUnless(shutil.which('cc'),'C99 compiler required')
    def test_single_native_process_and_same_deadline_order_fault(self):
        steps=[dict(at_ms=s['at_ms'],tick=True)if s['kind']=='tick'else
               {k:s[k]for k in ('at_ms','event','fields')}for s in self.case['steps']]
        stdin=commands(self.model,dict(steps=steps))
        expected_trace=[r for s in self.expected for r in s['trace']]
        with tempfile.TemporaryDirectory()as temporary:
            root=Path(temporary);source=render(self.model)
            for name,code in [('actual',source),('late-timer-fault',source.replace(
                'if(next<0||m->due[next]>at)break;','if(next<0||m->due[next]>=at)break;')),
                ('bool-json-type-fault',source.replace('text(out,m->v[4]?"true":"false");','number(out,m->v[4]);'))]:
                with self.subTest(name=name):
                    if name!='actual':self.assertNotEqual(code,source)
                    c=root/(name+'.c');exe=root/name;c.write_text(code)
                    compile_result=subprocess.run(['cc','-std=c99','-Wall','-Wextra','-Werror',str(c),'-o',str(exe)],
                        capture_output=True,text=True,timeout=60)
                    self.assertEqual(compile_result.returncode,0,compile_result.stderr)
                    result=subprocess.run([str(exe)],input=stdin,capture_output=True,text=True,timeout=30)
                    self.assertFalse(result.stderr)
                    rows=[json.loads(line)for line in result.stdout.splitlines()]
                    actual=[dict(rule=r['transition'],event=r['event'],at_ms=r['time_ms'],
                        after=dict(r['after'],now_ms=r['time_ms']),emitted=r['emitted'])
                        for r in rows if r['status']=='transition']
                    if name!='actual':
                        self.assertFalse(same_value(actual,expected_trace))
                        continue
                    # Exit1 is the declared final backward-time rejection, not failure to execute.
                    self.assertEqual(result.returncode,1)
                    self.assertTrue(same_value(actual,expected_trace))
                    replies=[r for r in rows if r['status']!='transition']
                    self.assertEqual(len(replies),11)
                    self.assertEqual(replies[0]['snapshot'],{k:v for k,v in self.case['initial'].items()if k!='now_ms'})
                    for reply,expected in zip(replies[1:],self.expected):
                        self.assertEqual(reply['status'],expected['status'])
                        self.assertTrue(same_value(reply['snapshot'],{k:v for k,v in expected['after'].items()if k!='now_ms'}))
                    self.assertEqual(replies[-1]['failure'],'nonmonotonic_time')
                    # Reply snapshots do not directly report clock. Transition clocks,
                    # timer deadlines and the later backwards-time rejection are checked.
