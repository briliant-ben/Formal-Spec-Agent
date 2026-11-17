"""Typed operators, full-byte literals, actual kernel and compiler boundaries."""
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
from formal_spec_agent import lean_typed as typed
from formal_spec_agent.lean_typed_native import render_runtime
from protocol_lab.ir import load,Machine,evaluate
from protocol_lab.codegen import render
from protocol_lab.codegen.execute import commands

ROOT=Path(__file__).resolve().parents[1];EX=ROOT/'examples/lean-values'
LEAN=os.environ.get('FSA_LEAN')or shutil.which('lean')


def write(p,v):p.write_text(json.dumps(v,indent=2)+'\n')


class TypedTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.root=Path(self.temp.name);self.w=self.root/'workspace';shutil.copytree(EX,self.w)
        self.task=self.w/'task.json';self.t=json.loads(self.task.read_text());self.m=load(self.w/'model.json')
    def tearDown(self):self.temp.cleanup()
    def prepare(self,draft=False):return gate.prepare(self.task,self.w,gate.sha(self.task),draft=draft)
    def rebind(self):
        t=json.loads(self.task.read_text());t['model_sha256']=gate.sha(self.w/'model.json');write(self.task,t)
        s,_,_=self.prepare(True);t['approved_sha256']=hashlib.sha256(s.encode()).hexdigest();write(self.task,t)

    def test_all_operator_and_value_kinds_are_reified_without_projection(self):
        view=typed.View(self.m).build();source,goals,inputs=self.prepare()
        self.assertEqual(view.operators,typed.SUPPORTED_OPS);self.assertEqual(len(view.operators),26)
        self.assertEqual(len(goals),59);self.assertIn('checksum_range',goals)
        for kind in typed.KINDS.values():self.assertIn('.'+kind,source)
        self.assertIn('List.replicate 4096',source);self.assertIn('Char.ofNat 0',source)
        self.assertIn('tool/lean/TypedIR.lean',inputs);self.assertNotIn('tool/lean/EfsmSubset.lean',inputs)
        self.assertLess(len(view.nodes),len(view.roots)*4)

    def test_reference_values_match_independent_frozen_cases(self):
        # No expectations are synthesized here. The source fixture was frozen
        # before execution; this is an independent reference implementation.
        view=typed.View(self.m).build()
        for c in self.t['cases']:
            r=view.roots[c['target']];machine=Machine(self.m,c['context']['variables']);machine.state=c['context']['state']
            machine.timers={n:0 for n in c['context']['active_timers']}
            _,ri,ai=c['target'].split('_');expr=self.m['transitions'][int(ri)]['actions'][int(ai)]['set']['value']
            actual=evaluate(expr,machine,dict(name=r['event'],fields=c['context']['fields']))
            self.assertEqual(actual,c['expected'],c['target'])

    def test_mixed_fields_are_shared_by_kind_and_slot_not_unscoped_names(self):
        m=copy.deepcopy(self.m);m['events']['another']=dict(origin='application',fields={'offset':'bytes','other':'int'})
        v=typed.View(m);a=v.expr({'event':'offset'},'sample');b=v.expr({'event':'offset'},'another')
        self.assertNotEqual(a,b);self.assertEqual(v.nodes[a][1],'int');self.assertEqual(v.nodes[b][1],'bytes')
        self.assertEqual(v.expr({'event':'other'},'another'),v.expr({'event':'count'},'sample'))
        m['events']['shifted']=dict(origin='application',fields={'unused':'bool','offset':'int'})
        self.assertNotEqual(v.expr({'event':'offset'},'shifted'),a)
        with self.assertRaises(ValueError):v.expr({'event':'missing'},'sample')

    def test_literal_content_and_unicode_scalar_domain(self):
        s=typed.literal([7]*4090+[0,128,255,6,2,0],'bytes')
        self.assertIn('List.replicate 4090',s);self.assertIn('⟨128, by decide⟩',s)
        self.assertIn('Char.ofNat 24320',typed.literal('开\n\0','string'))
        for value,kind in [('\ud800','string'),([256],'bytes'),(-1,'seq32'),(True,'int')]:
            with self.assertRaises(ValueError):typed.literal(value,kind)

    def test_unknown_ops_clock_rational_and_bad_signatures_refuse(self):
        v=typed.View(self.m)
        for expr in [dict(op='unknown',args=[]),dict(op='add',args=[True,1]),dict(op='ite',args=[True,1,False]),dict(clock_ms=True),dict(rat=[1,2])]:
            with self.assertRaises(ValueError):v.expr(expr,'sample')
        m=copy.deepcopy(self.m);m['semantics']='flat-efsm-atomic-ordered-clock-v3'
        with self.assertRaises(ValueError):typed.View(m)
        m=copy.deepcopy(self.m);m['ir_version']='0.5'
        with self.assertRaisesRegex(ValueError,'IR0.6'):typed.View(m).expr(dict(op='bytes_pack32be_mod',args=[1]))

    def test_task_pins_context_schema_and_operator_coverage(self):
        original=self.task.read_bytes()
        for key in ['adapter_sha256','model_sha256','approved_sha256']:
            t=json.loads(original);t[key]='0'*64;write(self.task,t)
            with self.assertRaises(ValueError):self.prepare()
        t=json.loads(original);t['cases']=[t['cases'][0]];write(self.task,t)
        with self.assertRaisesRegex(ValueError,'Every model operator'):self.prepare(True)
        t=json.loads(original);t['cases'][0]['context']['fields']['extra']=1;write(self.task,t)
        with self.assertRaisesRegex(ValueError,'schema mismatch'):self.prepare(True)

    def test_runtime_builder_has_no_oracle_channel(self):
        view=typed.View(self.m).build();inputs=[dict(target=c['target'],context=c['context'])for c in self.t['cases']]
        data,runner=render_runtime(view,inputs)
        self.assertNotIn('witness_',data);self.assertNotIn('Prop :=',data)
        self.assertNotIn('import Approved',runner)
        with self.assertRaisesRegex(ValueError,'inputs only'):render_runtime(view,self.t['cases'])
        bad=copy.deepcopy(self.t);bad['cases'][0]['expected']=999
        same=render_runtime(view,[dict(target=c['target'],context=c['context'])for c in bad['cases']])
        self.assertEqual((data,runner),same)

    @unittest.skipUnless(shutil.which('cc'),'C99 compiler required')
    def test_independent_standalone_C_matches_default_literal_operator_values(self):
        c=self.root/'subject.c';c.write_text(render(self.m));exe=self.root/'subject'
        subprocess.run(['cc','-std=c99','-Wall','-Wextra','-Werror',str(c),'-o',str(exe)],check=True,capture_output=True)
        context=self.t['cases'][0]['context'];scenario=dict(steps=[dict(at_ms=0,event='sample',fields=context['fields'])])
        p=subprocess.run([str(exe)],input=commands(self.m,scenario),text=True,capture_output=True,timeout=10)
        self.assertEqual(p.returncode,0,p.stderr)
        row=next(r for r in map(json.loads,p.stdout.splitlines())if r['status']=='transition')
        fields=row['emitted'][0]['fields']
        for i,c in enumerate(self.t['cases'][:29]):
            variable=self.m['transitions'][0]['actions'][i]['set']['var'];self.assertEqual(fields['value_'+variable.removeprefix('result_')],c['expected'])

    def test_resource_error_and_restricted_equational_proof_steps(self):
        self.assertTrue(gate.resource_failure(1,'Proofs.lean:9:2: error: maximum recursion depth has been reached',''))
        self.assertFalse(gate.resource_failure(1,'Proofs.lean:9:2: error: unsolved goals',''))
        self.assertIn('rw [FormalSpecAgent.ValueOps.fold16]', '\n'.join(gate.proof_lines([{'attempt':[{'rewrite':['FormalSpecAgent.ValueOps.fold16']}]}])))
        for step in [{'rewrite':['bad; run_tac']},{'attempt':[]},{'simp_only':['sorry']}]:
            with self.assertRaises(ValueError):gate.proof_lines([step])

    @unittest.skipUnless(LEAN,'Actual Lean required')
    def test_actual_kernel_and_fresh_recheck(self):
        r=gate.check(self.task,self.w,self.root/'check',self.w/'proofs.json',gate.sha(self.task),LEAN)
        self.assertEqual(r['status'],'checked_typed_expression_contract');self.assertTrue(r['typed_expression_contract_checked']);self.assertFalse(r['efsm_contract_checked'])
        again=gate.verify(self.root/'check',self.task,self.w,self.root/'recheck',gate.sha(self.task),LEAN)
        self.assertEqual(again['status'],r['status'])

    @unittest.skipUnless(LEAN,'Actual Lean required')
    def test_seq_distance_direction_mutant_fails_rebound_kernel_contract(self):
        m=json.loads((self.w/'model.json').read_text());a=m['transitions'][0]['actions'][14]['set']['value']['args'];a.reverse();write(self.w/'model.json',m);self.rebind()
        r=gate.check(self.task,self.w,self.root/'wrong-sequence',self.w/'proofs.json',gate.sha(self.task),LEAN)
        self.assertEqual(r['classification'],'proof_failure')

    @unittest.skipUnless(LEAN,'Actual Lean required')
    def test_changed_oracle_is_rejected_and_types_are_not_EFSM_proofs(self):
        t=json.loads(self.task.read_text());t['cases'][0]['expected']=-251;write(self.task,t);self.rebind()
        r=gate.check(self.task,self.w,self.root/'wrong-oracle',self.w/'proofs.json',gate.sha(self.task),LEAN)
        self.assertEqual(r['classification'],'proof_failure')
        self.assertFalse(r.get('efsm_contract_checked',False))

    @unittest.skipUnless(LEAN,'Actual Lean and matching C compiler required')
    def test_compiled_Lean_reference_and_certificate_integrity(self):
        from formal_spec_agent.lean_native import run
        out=self.root/'native';r=run(self.task,self.w,out,self.w/'proofs.json',gate.sha(self.task),LEAN)
        self.assertEqual(r['status'],'native_reference_match');self.assertEqual(len(r['observed']),56)
        self.assertIn(dict(kind='string',value=[24320,10,0]),r['observed'])
        self.assertEqual(r['observed'][-1]['value'],[7]*4090+[0,128,255,6,2,0])
        gate.inspect_certificate(out/'certificate',self.task,self.w,gate.sha(self.task))
        self.assertNotIn('Approved.lean',r['runtime_sources']);self.assertFalse(r['compiler_correctness_proved'])

    @unittest.skipUnless(LEAN,'Actual Lean required')
    def test_actual_pinned_TCPIP_model_typecheck_has_no_safety_claim(self):
        model=os.environ.get('FSA_TCPIP_MODEL')
        if not model:
            if os.environ.get('FSA_TCPIP_REQUIRED')=='1':self.fail('Pinned TCPIP model required by this CI channel')
            self.skipTest('Pinned external TCPIP model supplied by dedicated CI')
        path=Path(model);pin='7d5a82541ea55cde3ff39b2e1cf883f6c9f942f5dc535a2736e69044d9e154a5'
        r=typed.check_types(path,path.parent,self.root/'full-case',pin,LEAN)
        self.assertEqual(r['status'],'typed_ir_view_checked');self.assertEqual(r['view']['rules'],335);self.assertEqual(len(r['view']['operators']),26)
        self.assertEqual(len(r['view']['root_bindings']),r['view']['roots'])
        self.assertIn('rule',r['view']['root_bindings']['guard_0']['origin'])
        self.assertFalse(r['efsm_safety_proved']);self.assertFalse(r['compiler_correctness_proved'])
