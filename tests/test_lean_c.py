"""Per-output C parsing, frozen provenance and real Lean refinement checks."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from formal_spec_agent import lean_backend as gate
from formal_spec_agent import lean_c
from protocol_lab.ir import load,Machine
from protocol_lab.codegen import render
from protocol_lab.codegen.execute import commands

ROOT=Path(__file__).resolve().parents[1];EX=ROOT/'examples/lean-c-read'
LEAN=os.environ.get('FSA_LEAN')or shutil.which('lean')


def write(p,v):p.write_text(json.dumps(v,indent=2)+'\n')


class CExpressionTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.root=Path(self.temp.name);self.w=self.root/'workspace';shutil.copytree(EX,self.w)
        self.task=self.w/'task.json';self.source=self.w/'generated/protocol.c';self.m=load(self.w/'model.json');self.fields=self.m['events']['inspect']['fields']
    def tearDown(self):self.temp.cleanup()
    def parse(self,source=None):return lean_c.parse_expression(source or self.source.read_text(),self.fields,0,0)
    def prepare(self,draft=False):return gate.prepare(self.task,self.w,gate.sha(self.task),draft=draft)
    def rebound_source(self,source):
        self.source.write_text(source);t=json.loads(self.task.read_text());t['c_source']['sha256']=gate.sha(self.source);write(self.task,t)
        draft,_,_=self.prepare(True);t['approved_sha256']=hashlib.sha256(draft.encode()).hexdigest();write(self.task,t)

    def test_actual_C_and_IR_views_are_independently_reified(self):
        self.assertEqual(render(self.m),self.source.read_text())
        parsed,view=self.parse();original=lean_c.ir_tree(self.m['transitions'][0]['actions'][0]['set']['value'],self.m,'inspect')
        self.assertEqual(parsed,original)
        self.assertIn('byte_at_or_zero',view['expression_tokens'])
        approved,goals,inputs=self.prepare();self.assertEqual(len(goals),11)
        self.assertIn('def actualC',approved);self.assertIn('def originalIR',approved)
        self.assertIn('tool/lean_c.py',inputs);self.assertIn('C_runtime',inputs);self.assertIn('C_harness',inputs)

    def test_changed_C_or_runtime_is_not_silently_accepted(self):
        self.source.write_text(self.source.read_text().replace('f[1]','INT64_C(0)'))
        with self.assertRaisesRegex(ValueError,'C digest'):self.prepare()
        original=(EX/'generated/protocol.c').read_text()
        wrong=original.replace('return a.data[(size_t)offset];','return a.data[0];')
        with self.assertRaisesRegex(ValueError,'runtime differs'):self.parse(wrong)

    def test_preprocessor_splicing_and_unknown_calls_refused(self):
        original=self.source.read_text()
        for fragment in ['#define f another_pointer\n','??=define f another_pointer\n','\\\n']:
            with self.subTest(fragment=fragment):
                changed=original.replace('static int rule_action_0',fragment+'static int rule_action_0')
                with self.assertRaises(ValueError):self.parse(changed)
        changed=original.replace('byte_at_or_zero(bf[0],f[1])','unknown_callback(bf[0],f[1])')
        with self.assertRaisesRegex(ValueError,'Unsupported C expression'):self.parse(changed)

    def test_c99_octal_literals_and_wrong_field_types_are_refused(self):
        original=self.source.read_text()
        for a,b in [(':INT64_C(0)',':010'),('byte_at_or_zero(bf[0],f[1])','byte_at_or_zero(bf[0],f[2])')]:
            changed=original.replace(a,b);self.assertNotEqual(changed,original)
            with self.assertRaises(ValueError):self.parse(changed)

    def test_pure_shared_helper_is_expanded_and_bad_arguments_or_cycles_refuse(self):
        original=self.source.read_text();call='byte_at_or_zero(bf[0],f[1])'
        header='static inline int64_t shared_expr_999(Machine *m,int64_t *f,Bytes *bf) { (void)m; (void)f; (void)bf; return '
        changed=original.replace('static int rule_guard_0',header+call+'; }\nstatic int rule_guard_0').replace('?'+call+' :','?shared_expr_999(m,f,bf) :')
        # The generator uses compact operators without whitespace.
        changed=changed.replace('?'+call+':','?shared_expr_999(m,f,bf):')
        parsed,view=self.parse(changed);self.assertEqual(parsed,self.parse()[0]);self.assertIn('shared_expr_999',view['expanded_helpers'])
        with self.assertRaises(ValueError):self.parse(changed.replace('shared_expr_999(m,f,bf)','shared_expr_999(m,bf,f)'))
        with self.assertRaisesRegex(ValueError,'cycle'):self.parse(changed.replace('return '+call+';','return shared_expr_999(m,f,bf);'))

    def test_unterminated_lexical_forms_cannot_fabricate_a_selected_function(self):
        original=self.source.read_text()
        for prefix in ['/* unclosed comment\n','"unclosed string\n']:
            altered=original.replace('static int rule_action_0',prefix+'static int rule_action_0')
            with self.assertRaises(ValueError):self.parse(altered)

    def test_unsupported_IR_arithmetic_is_refused(self):
        with self.assertRaisesRegex(ValueError,'Unsupported IR operator'):
            lean_c.ir_tree(dict(op='add',args=[1,2]),self.m,'inspect')

    def test_parser_epoch_and_unsealed_draft_cannot_self_approve(self):
        t=json.loads(self.task.read_text());old=self.task.read_bytes()
        for name in ['parser_sha256','approved_sha256']:
            t=json.loads(old);t[name]='0'*64;write(self.task,t)
            with self.assertRaises(ValueError):self.prepare()
        self.task.write_bytes(old)

    def test_native_witness_domain_rejects_large_indices(self):
        old=self.task.read_bytes()
        for n in [2**63,-(2**63)-1]:
            t=json.loads(old);t['witnesses'][1]['fields']['index']=n;write(self.task,t)
            with self.assertRaisesRegex(ValueError,'outside native domain'):self.prepare(True)
        for n in [-(2**63),2**63-1]:
            t=json.loads(old);t['witnesses'][1]['fields']['index']=n;write(self.task,t)
            self.prepare(True)
        self.task.write_bytes(old)

    def test_each_helper_parameter_macro_and_impure_return_is_refused(self):
        original=self.source.read_text()
        for name in ['m','f','bf']:
            altered=original.replace('static int rule_action_0','#define '+name+' malicious\nstatic int rule_action_0')
            with self.assertRaisesRegex(ValueError,'preprocessing'):self.parse(altered)
        helper='static inline int64_t shared_expr_999(Machine *m,int64_t *f,Bytes *bf) { (void)m; (void)f; (void)bf; return malicious(); }\n'
        altered=original.replace('static int rule_guard_0',helper+'static int rule_guard_0').replace('byte_at_or_zero(bf[0],f[1])','shared_expr_999(m,f,bf)')
        with self.assertRaisesRegex(ValueError,'Unsupported C expression'):self.parse(altered)

    @unittest.skipUnless(shutil.which('cc'),'C99 compiler required')
    def test_generated_native_C_matches_independent_literals_and_reference(self):
        # Only the trusted generator output, not an arbitrary provided C artifact,
        # is compiled/executed by this native regression.
        c=self.root/'native.c';c.write_text(render(self.m));exe=self.root/'native'
        subprocess.run(['cc','-std=c99','-Wall','-Wextra','-Werror',str(c),'-o',str(exe)],check=True,capture_output=True)
        witnesses=json.loads(self.task.read_text())['witnesses'];scenario=dict(steps=[dict(at_ms=0,event='inspect',fields=w['fields'])for w in witnesses])
        p=subprocess.run([str(exe)],input=commands(self.m,scenario),text=True,capture_output=True,timeout=10);self.assertEqual(p.returncode,0)
        rows=[r for r in map(json.loads,p.stdout.splitlines())if r['status']=='transition'];self.assertEqual(len(rows),len(witnesses))
        machine=Machine(self.m)
        for row,w in zip(rows,witnesses):
            machine.dispatch('inspect',w['fields'],0)
            expected=[dict(message='observed',fields=dict(value=w['expected']))]
            self.assertEqual(row['emitted'],expected);self.assertEqual(machine.trace[-1]['emitted'],expected)


@unittest.skipUnless(LEAN,'Optional pinned Lean checker unavailable')
class CKernelTests(unittest.TestCase):
    setUp=CExpressionTests.setUp;tearDown=CExpressionTests.tearDown;prepare=CExpressionTests.prepare;rebound_source=CExpressionTests.rebound_source
    def check(self,out):return gate.check(self.task,self.w,self.root/out,self.w/'proofs.json',gate.sha(self.task),LEAN)

    def test_actual_generated_expression_refinement_checks_and_rechecks(self):
        r=self.check('good');self.assertEqual(r['status'],'checked_expression_contract');self.assertTrue(r['c_expression_model_refinement_checked'])
        again=gate.verify(self.root/'good',self.task,self.w,self.root/'recheck',gate.sha(self.task),LEAN)
        self.assertEqual(again['status'],'checked_expression_contract');self.assertFalse(again['compiler_correctness_proved'])

    def test_compiled_Lean_reference_generates_and_runs_C(self):
        from formal_spec_agent.lean_native import run
        r=run(self.task,self.w,self.root/'native-reference',self.w/'proofs.json',gate.sha(self.task),LEAN)
        self.assertEqual(r['status'],'native_reference_match')
        self.assertEqual(r['observed'],[65,0,0,0,255])
        c=(self.root/'native-reference/runtime/Runner.c').read_text()
        self.assertIn('lean/lean.h',c)
        self.assertEqual(r['runtime'],'Lean runtime required')
        self.assertFalse(r['compiler_correctness_proved'])
        again=gate.verify(self.root/'native-reference/certificate',self.task,self.w,self.root/'native-certificate-recheck',gate.sha(self.task),LEAN)
        self.assertEqual(again['status'],'checked_expression_contract')

    def test_rebound_wrong_index_fails_Lean_not_just_old_hash(self):
        self.rebound_source(self.source.read_text().replace('byte_at_or_zero(bf[0],f[1])','byte_at_or_zero(bf[0],INT64_C(0))'))
        r=self.check('mutant');self.assertEqual(r['status'],'fail');self.assertEqual(r['failed_module'],'Proofs')

    def test_changed_shared_helper_body_fails_even_with_updated_source_binding(self):
        original=self.source.read_text();call='byte_at_or_zero(bf[0],f[1])'
        helper='static inline int64_t shared_expr_999(Machine *m,int64_t *f,Bytes *bf) { (void)m; (void)f; (void)bf; return byte_at_or_zero(bf[0],INT64_C(0)); }\n'
        changed=original.replace('static int rule_guard_0',helper+'static int rule_guard_0').replace('?'+call+':','?shared_expr_999(m,f,bf):')
        self.rebound_source(changed);r=self.check('shared-mutant');self.assertEqual(r['status'],'fail')
