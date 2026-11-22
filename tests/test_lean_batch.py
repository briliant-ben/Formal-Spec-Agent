"""Frozen batch semantics: independent reference/native regression before proofs."""
import copy
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from protocol_lab.ir import load,Machine,ModelError,Conflict,Uncovered
from protocol_lab.codegen import render
from protocol_lab.codegen.execute import commands

EX=Path(__file__).resolve().parents[1]/'examples/lean-batch'
CASES_SHA='1a13b99dee31ddbd71f4d05e6528e378989ec36881eaf4eedcf05d0030084bac'


def observe_reference(model,case):
    initial=case['initial'];obj=Machine(model,initial['variables']);obj.state=initial['state'];obj.timers=initial['timers'].copy();obj.now_ms=initial['now_ms'];obj.check_invariants();results=[]
    for step in case['steps']:
        before=copy.deepcopy(obj.snapshot());clock=obj.now_ms;trace=copy.deepcopy(obj.trace);fault=None
        try:
            if step['kind']=='tick':obj.tick(step['at_ms'])
            else:obj.dispatch(step['event'],step['fields'],step['at_ms'])
        except Conflict:fault='conflict'
        except Uncovered:fault='uncovered'
        except ModelError as e:
            message=str(e)
            categories={'Timer duration must be positive':'badDelay','Invariant failed:':'invariant','Timer events cannot be injected':'timerInjection','Time must be monotonic':'time'}
            matches=[fault for text,fault in categories.items()if text in message]
            if len(matches)!=1:raise
            fault=matches[0]
        if fault:
            assert obj.snapshot()==before and obj.now_ms==clock and obj.trace==trace
            results.append(dict(status='error',fault=fault))
        else:
            rows=[dict(rule=t['transition'],event=t['event'],at_ms=t['time_ms'],after=dict(t['after'],now_ms=t['time_ms']),emitted=t['emitted'])for t in obj.trace[len(trace):]]
            results.append(dict(status='ok',after=dict(obj.snapshot(),now_ms=obj.now_ms),trace=rows))
    return results


class BatchFixtureTests(unittest.TestCase):
    def setUp(self):self.model=load(EX/'model.json');self.cases=json.loads((EX/'cases.json').read_text())

    def test_independent_frozen_cases_cover_whole_batch_failures_and_rearming(self):
        self.assertEqual(hashlib.sha256((EX/'cases.json').read_bytes()).hexdigest(),CASES_SHA)
        self.assertEqual(len(self.cases),7);self.assertEqual(sum(len(c['steps'])for c in self.cases),22)
        by_id={c['id']:c for c in self.cases}
        self.assertEqual(by_id['second-timer-error-discards-first']['steps'][2]['expected'],dict(status='error',fault='badDelay'))
        rearmed=by_id['positive-rearming-to-finite-target']['steps'][1]['expected'];self.assertEqual([r['at_ms']for r in rearmed['trace']],[2,4,6]);self.assertEqual(rearmed['after']['now_ms'],10)
        self.assertEqual(len(by_id['full-buffer-batch']['steps'][0]['fields']['payload']),4096)

    def test_actual_reference_matches_all_literals_and_error_atomicity(self):
        for case in self.cases:self.assertEqual(observe_reference(self.model,case),[s['expected']for s in case['steps']],case['id'])

    def test_wrong_timer_order_or_leaked_prefix_breaks_frozen_oracle(self):
        expected=self.cases[0]['steps'][1]['expected'];reversed_rows=copy.deepcopy(expected);reversed_rows['trace'].reverse();self.assertNotEqual(expected,reversed_rows)
        # A success prefix cannot be reported as a successful partial tick when
        # the second timer or external event fails. No expected value is reset.
        bad=copy.deepcopy(self.cases[2]);bad['steps'][2]['expected']=dict(status='ok',after=expected['trace'][0]['after'],trace=[expected['trace'][0]])
        self.assertNotEqual(observe_reference(self.model,bad),[s['expected']for s in bad['steps']])

    def test_explicit_error_snapshot_is_compared_without_entering_runtime_source(self):
        from formal_spec_agent.lean_batch import BatchView
        from formal_spec_agent.lean_batch_native import expected_values, input_cases, render_runtime

        timed_cell = EX.parent/'lean-timed-efsm'
        frozen = json.loads((timed_cell/'cases.json').read_text())
        view = BatchView(load(timed_cell/'model.json'))
        baseline = expected_values(view, frozen)
        self.assertEqual(baseline[9]['status'], 'error')
        self.assertEqual(baseline[9]['after']['now_ms'], 35)
        wrong_clock = copy.deepcopy(frozen)
        wrong_clock[0]['steps'][9]['expected']['after']['now_ms'] = 34
        self.assertNotEqual(expected_values(view, wrong_clock), baseline)
        self.assertEqual(render_runtime(view, input_cases(wrong_clock)),
                         render_runtime(view, input_cases(frozen)))
        wrong_clock[0]['steps'][9]['expected']['trace'] = [baseline[8]['trace'][0]]
        with self.assertRaisesRegex(ValueError, 'empty trace'):
            expected_values(view, wrong_clock)

    @unittest.skipUnless(shutil.which('cc'),'C99 compiler required')
    def test_standalone_C_matches_all_frozen_operation_prefixes(self):
        with tempfile.TemporaryDirectory()as temp:
            root=Path(temp);c=root/'subject.c';exe=root/'subject';c.write_text(render(self.model));subprocess.run(['cc','-std=c99','-Wall','-Wextra','-Werror',str(c),'-o',str(exe)],check=True,capture_output=True)
            base=dict(state=self.model['initial_state'],now_ms=0,variables={n:v['initial']for n,v in self.model['variables'].items()},timers={});count=0
            for case in self.cases:
                prefix=[];expected_trace=[];state=case['initial']
                if state!=base:
                    # Explicit unit setup, never presented as a live single PID.
                    setup=self.cases[0]['steps'][0];self.assertEqual(setup['expected']['after'],state)
                    prefix=[dict(event=setup['event'],fields=setup['fields'],at_ms=setup['at_ms'])];expected_trace=copy.deepcopy(setup['expected']['trace'])
                for step in case['steps']:
                    operation=dict(tick=True,at_ms=step['at_ms'])if step['kind']=='tick'else dict(event=step['event'],fields=step['fields'],at_ms=step['at_ms'])
                    p=subprocess.run([str(exe)],input=commands(self.model,dict(steps=prefix+[operation])),text=True,capture_output=True,timeout=20);rows=list(map(json.loads,p.stdout.splitlines()));expected=step['expected']
                    if p.returncode==0:
                        self.assertEqual(expected['status'],'ok');prefix.append(operation);expected_trace+=expected['trace'];state=expected['after']
                    else:self.assertEqual(p.returncode,1);self.assertEqual(expected['status'],'error')
                    actual=[dict(rule=r['transition'],event=r['event'],at_ms=r['time_ms'],after=dict(r['after'],now_ms=r['time_ms']),emitted=r['emitted'])for r in rows if r['status']=='transition']
                    self.assertEqual(actual,expected_trace);self.assertEqual(rows[-1]['snapshot'],{k:v for k,v in state.items()if k!='now_ms'});count+=1
            self.assertEqual(count,22)
