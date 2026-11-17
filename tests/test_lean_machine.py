"""Actual typed action, conflict, error rollback and scheduled timer evidence."""
import copy
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from formal_spec_agent import lean_backend as gate
from formal_spec_agent import lean_machine as machine
from formal_spec_agent import lean_machine_native as native
from protocol_lab.ir import load,Machine,ModelError,Conflict,Uncovered
from protocol_lab.codegen import render
from protocol_lab.codegen.execute import commands

ROOT=Path(__file__).resolve().parents[1];EX=ROOT/'examples/lean-machine'
LEAN=os.environ.get('FSA_LEAN')or shutil.which('lean')


def write(p,v):p.write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n')


def reference(m,case):
    initial=case['initial'];obj=Machine(m,initial['variables']);obj.state=initial['state'];obj.timers=initial['timers'].copy();obj.now_ms=initial['now_ms'];obj.check_invariants();results=[]
    for step in case['steps']:
        before=copy.deepcopy(obj.snapshot());clock=obj.now_ms;trace=copy.deepcopy(obj.trace);fault=None
        # This wrapper is the explicitly admitted microstep domain, not a claim
        # that Machine.dispatch rejects due timers. It delegates admitted work
        # to actual public reference operations, without editing protocol logic.
        if step['at_ms']<obj.now_ms:fault='time'
        elif step['kind']=='external'and m['events'][step['event']]['origin']=='timer':fault='timerInjection'
        elif step['kind']=='external'and any(t<=step['at_ms']for t in obj.timers.values()):fault='pendingTimer'
        elif step['kind']=='timer'and not obj.timers:fault='noTimer'
        elif step['kind']=='timer'and min(obj.timers.values())!=step['at_ms']:fault='time'
        else:
            try:
                if step['kind']=='timer':obj.step_timer(step['at_ms'])
                else:obj.dispatch(step['event'],step['fields'],step['at_ms'])
            except Conflict:fault='conflict'
            except Uncovered:fault='uncovered'
            except ModelError as e:
                if 'Timer duration must be positive'in str(e):fault='badDelay'
                elif 'Invariant failed:'in str(e):fault='invariant'
                else:raise
        if fault:
            assert obj.snapshot()==before and obj.now_ms==clock and obj.trace==trace
            actual=dict(status='error',fault=fault)
        else:
            row=obj.trace[-1];actual=dict(status='ok',rule=row['transition'],after=dict(obj.snapshot(),now_ms=obj.now_ms),emitted=row['emitted'])
        results.append(actual)
    return results


class MachineTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.root=Path(self.temp.name);self.w=self.root/'workspace';shutil.copytree(EX,self.w);self.task=self.w/'task.json';self.t=json.loads(self.task.read_text());self.m=load(self.w/'model.json')
    def tearDown(self):self.temp.cleanup()
    def prepare(self,draft=False):return gate.prepare(self.task,self.w,gate.sha(self.task),draft=draft)
    def rebind(self):
        t=json.loads(self.task.read_text());t['model_sha256']=gate.sha(self.w/'model.json');write(self.task,t);s,_,_=self.prepare(True);t['approved_sha256']=hashlib.sha256(s.encode()).hexdigest();write(self.task,t)

    def test_complete_typed_actions_and_sorted_timer_identity(self):
        v=machine.MachineView(self.m);s,goals,inputs=self.prepare()
        self.assertEqual(v.timers,['a','z']);self.assertEqual(list(self.m['timers']),['z','a']);self.assertEqual(len(goals),29)
        self.assertIn('TypedMachine.Action.assign .sequence',s);self.assertIn('MachineObserve.outcome',s)
        self.assertEqual(gate.contract_status(inputs),'checked_scheduled_microstep_contract');self.assertNotEqual(gate.contract_status(inputs),'checked_efsm_contract')
        # Reordering declarations cannot change timer identity or tie behavior.
        m=copy.deepcopy(self.m);m['timers']=dict(reversed(list(m['timers'].items())));self.assertEqual(v.source(),machine.MachineView(m).source())

    def test_reference_all_frozen_values_errors_and_same_deadline_order(self):
        cases=json.loads((self.w/'cases.json').read_text());self.assertEqual(len(cases),7);count=0
        for c in cases:
            expected=[s['expected']for s in c['steps']];self.assertEqual(reference(self.m,c),expected,c['id']);count+=len(expected)
        self.assertEqual(count,18)

    def test_inputs_only_runtime_has_no_expected_channel(self):
        v=machine.MachineView(self.m);a=native.input_cases(self.t['cases']);s,r=native.render_runtime(v,a)
        self.assertNotIn('def witness_',s);self.assertNotIn('Prop :=',s);self.assertNotIn('import Approved',r)
        with self.assertRaises(ValueError):native.render_runtime(v,self.t['cases'])
        t=copy.deepcopy(self.t);t['cases'][0]['steps'][0]['expected']['after']['variables']['n']=999
        self.assertEqual((s,r),native.render_runtime(v,native.input_cases(t['cases'])))

    def test_invalid_dimensions_unknown_actions_and_unsupported_semantics_refuse(self):
        v=machine.MachineView(self.m);s=copy.deepcopy(self.t['cases'][0]['initial'])
        for key,value in [('timers',{'unknown':1}),('now_ms',-1),('variables',{})]:
            bad=copy.deepcopy(s);bad[key]=value
            with self.assertRaises(ValueError):v.snapshot(bad)
        with self.assertRaises(ValueError):v.command(dict(kind='external',event='start',fields={},at_ms=0),'initial')
        m=copy.deepcopy(self.m);m['transitions'][0]['actions'].append({'callback':'hidden'})
        with self.assertRaises(ValueError):machine.MachineView(m)
        m=copy.deepcopy(self.m);m['semantics']='flat-efsm-atomic-ordered-clock-v3'
        with self.assertRaises(ValueError):machine.MachineView(m)

    def test_all_approval_pins_and_frozen_oracles_are_bound(self):
        original=self.task.read_bytes()
        for k in ['model_sha256','adapter_sha256','approved_sha256']:
            t=json.loads(original);t[k]='0'*64;write(self.task,t)
            with self.assertRaises(ValueError):self.prepare()
        self.task.write_bytes(original);(self.w/'spec.md').write_text('changed')
        with self.assertRaisesRegex(ValueError,'source digest'):self.prepare()

    @unittest.skipUnless(shutil.which('cc'),'C99 compiler required')
    def test_actual_standalone_C_uses_same_order_timers_full_bytes_and_rollback(self):
        c=self.root/'subject.c';exe=self.root/'subject';c.write_text(render(self.m));subprocess.run(['cc','-std=c99','-Wall','-Wextra','-Werror',str(c),'-o',str(exe)],check=True,capture_output=True)
        small=self.t['cases'][0];large=self.t['cases'][6]
        scenarios=[(dict(steps=[dict(event='start',fields={'payload':[0,128,255,7]},at_ms=0),dict(tick=True,at_ms=5)]),[small['steps'][i]['expected']for i in [0,2,3]]),(dict(steps=[dict(event='start',fields=large['steps'][0]['fields'],at_ms=0)]),[large['steps'][0]['expected']])]
        for scenario,expected in scenarios:
            p=subprocess.run([str(exe)],input=commands(self.m,scenario),text=True,capture_output=True,timeout=15);self.assertEqual(p.returncode,0,p.stderr)
            rows=[r for r in map(json.loads,p.stdout.splitlines())if r['status']=='transition'];actual=[dict(status='ok',rule=r['transition'],after=dict(r['after'],now_ms=r['time_ms']),emitted=r['emitted'])for r in rows];self.assertEqual(actual,expected)
        for event,fields in [('bad_delay',{'delay':0}),('bad_final',{}),('ambiguous',{}),('gap',{})]:
            p=subprocess.run([str(exe)],input=commands(self.m,dict(steps=[dict(event=event,fields=fields,at_ms=3)])),text=True,capture_output=True,timeout=10);rows=list(map(json.loads,p.stdout.splitlines()));self.assertEqual(p.returncode,1);self.assertEqual(rows[-1]['snapshot'],rows[0]['snapshot']);self.assertFalse(any(r['status']=='transition'for r in rows))

    @unittest.skipUnless(LEAN,'Actual Lean required')
    def test_actual_kernel_contract_and_fresh_recheck(self):
        r=gate.check(self.task,self.w,self.root/'check',self.w/'proofs.json',gate.sha(self.task),LEAN);self.assertEqual(r['status'],'checked_scheduled_microstep_contract');self.assertTrue(r['scheduled_microstep_contract_checked']);self.assertFalse(r['efsm_contract_checked']);self.assertFalse(r['typed_expression_contract_checked'])
        v=gate.verify(self.root/'check',self.task,self.w,self.root/'recheck',gate.sha(self.task),LEAN);self.assertEqual(v['status'],r['status'])
        raw=json.loads((self.root/'check/result.json').read_text());raw['efsm_contract_checked']=True;write(self.root/'check/result.json',raw)
        with self.assertRaisesRegex(ValueError,'EFSM claim'):gate.inspect_certificate(self.root/'check',self.task,self.w,gate.sha(self.task))

    @unittest.skipUnless(LEAN,'Actual Lean required')
    def test_rebound_wrong_write_order_is_rejected_by_kernel(self):
        m=json.loads((self.w/'model.json').read_text());m['transitions'][0]['actions'][2]['set']['value']=4;write(self.w/'model.json',m);self.rebind()
        r=gate.check(self.task,self.w,self.root/'mutant',self.w/'proofs.json',gate.sha(self.task),LEAN);self.assertEqual(r['status'],'fail');self.assertEqual(r['classification'],'proof_failure')

    @unittest.skipUnless(LEAN,'Actual Lean required')
    def test_compiled_Lean_reference_matches_all_snapshots_outputs_and_errors(self):
        r=native.run(self.w/'model.json',self.w,self.w/'cases.json',self.root/'native',gate.sha(self.w/'model.json'),gate.sha(self.w/'cases.json'),LEAN);self.assertEqual(r['status'],'scheduled_reference_match');self.assertEqual(len(r['observed']),18);self.assertFalse(r['kernel_literal_contract_checked']);self.assertFalse(r['efsm_safety_proved'])

    @unittest.skipUnless(LEAN and os.environ.get('FSA_TCPIP_MODEL'),'Actual pinned TCPIP model required')
    def test_all_pinned_TCPIP_rules_and_effects_compile_and_execute_frozen_trace(self):
        mf=Path(os.environ['FSA_TCPIP_MODEL']);m=load(mf);view=machine.MachineView(m);self.assertEqual(len(m['transitions']),335)
        provenance=json.loads((EX/'tcpip-provenance.json').read_text());self.assertEqual(gate.sha(EX/'tcpip-cases.json'),provenance['cases_sha256']);self.assertEqual(gate.sha(mf),'7d5a82541ea55cde3ff39b2e1cf883f6c9f942f5dc535a2736e69044d9e154a5')
        casefile=os.environ.get('FSA_TCPIP_MACHINE_CASES')or str(EX/'tcpip-cases.json')
        if not casefile:
            if os.environ.get('FSA_TCPIP_MACHINE_REQUIRED')=='1':self.fail('Pinned TCPIP scheduled fixture required')
            self.skipTest('Pinned TCPIP scheduled fixture not supplied')
        dest=self.root/'tcpip';dest.mkdir();shutil.copyfile(mf,dest/'model.json');shutil.copyfile(casefile,dest/'cases.json')
        r=native.run(dest/'model.json',dest,dest/'cases.json',self.root/'case-native',gate.sha(dest/'model.json'),gate.sha(dest/'cases.json'),LEAN);self.assertEqual(r['status'],'scheduled_reference_match');self.assertGreater(len(r['observed']),5);self.assertFalse(r['efsm_safety_proved'])
