"""Compiled regressions for expression factoring, including failure paths."""
import copy
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from protocol_lab.codegen import cstr, render
from protocol_lab.codegen.execute import commands, compare
from protocol_lab.ir import load

ROOT = Path(__file__).resolve().parents[1]


def op(name, *args):
    return dict(op=name, args=list(args))


def long_value(value):
    for _ in range(5):
        value = op('add', value, 0)
    return value


def model():
    m = load(ROOT/'examples/mailbox/model.json')
    m['variables']['x'] = dict(type='int', initial=0)
    m['messages']['number'] = dict(fields=dict(a='int', b='int'))
    return m


@unittest.skipUnless(shutil.which('cc'), 'C99 compiler required')
class SharedExpressionTests(unittest.TestCase):
    def check_models(self, m, scenarios, reference=True, optimize='-O0'):
        with tempfile.TemporaryDirectory() as tmp:
            scenarios = [dict(scenario_version='0.2', expect=dict(state='READY', timers={}), **s) for s in scenarios]
            results = []
            for sharing in (False, True):
                source = render(m, share_expressions=sharing)
                c = Path(tmp)/('shared.c' if sharing else 'expanded.c')
                c.write_text(source)
                exe = c.with_suffix('')
                subprocess.run(['cc', '-std=c99', '-Wall', '-Wextra', '-Werror', optimize, str(c), '-o', str(exe)], check=True, capture_output=True)
                runs = [subprocess.run([str(exe)], input=commands(m, s), text=True, capture_output=True, timeout=10) for s in scenarios]
                if reference:
                    for s, run in zip(scenarios, runs):
                        self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
                        self.assertEqual(compare(m, s, [json.loads(row) for row in run.stdout.splitlines()])['status'], 'match')
                results.append([(r.returncode, r.stdout, r.stderr) for r in runs])
            self.assertEqual(*results)
            return results[0]

    def test_sharing_shrinks_and_is_deterministic(self):
        m = model()
        e = long_value({'var': 'x'})
        m['transitions'][1]['actions'] = [dict(emit=dict(message='number', fields=dict(a=e, b=e)))]*4
        shared = render(m)
        self.assertIn('static inline int64_t shared_expr_', shared)
        self.assertLess(len(shared), len(render(m, share_expressions=False)))
        self.assertEqual(shared, render(json.loads(json.dumps(m))))
        self.check_models(m, [dict(steps=[dict(at_ms=0, event='clear')])])

    def test_reads_follow_ordered_writes_not_cached_values(self):
        m = model(); e = long_value({'var': 'x'})
        emit = dict(emit=dict(message='number', fields=dict(a=e, b=e)))
        m['transitions'][1]['actions'] = [dict(set=dict(var='x', value=1)), emit, dict(set=dict(var='x', value=2)), emit]
        self.check_models(m, [dict(steps=[dict(at_ms=0, event='clear'), dict(at_ms=1, event='clear')])], optimize='-O2')

    def test_short_circuit_and_conditional_do_not_eagerly_fail(self):
        m = model(); bad = long_value(op('add', (1 << 63)-1, 1))
        m['transitions'][1]['actions'] = [dict(emit=dict(message='number', fields=dict(a=op('ite', True, 7, bad), b=op('ite', False, bad, 9))))]
        duplicate = copy.deepcopy(m['transitions'][1]); duplicate['id'] = 'DISABLED'
        duplicate['guard'] = op('or', op('and', False, op('eq', bad, bad)), op('implies', True, False))
        m['transitions'].append(duplicate)
        self.check_models(m, [dict(steps=[dict(at_ms=0, event='clear')])])

    def test_overflow_and_byte_capacity_fail_atomically(self):
        for failure in ('integer_overflow', 'byte_capacity'):
            with self.subTest(failure=failure):
                m = model()
                if failure == 'integer_overflow':
                    e = long_value(op('add', (1 << 63)-1, 1))
                    actions = [dict(emit=dict(message='number', fields=dict(a=e, b=e)))]
                else:
                    e = op('bytes_concat', {'event': 'data'}, {'event': 'data'})
                    actions = [dict(set=dict(var='buffer', value=e)), dict(set=dict(var='buffer', value=e))]
                m['transitions'][0]['guard'] = True
                m['transitions'][0]['actions'] = [dict(set=dict(var='x', value=99))] + actions
                rows = self.check_models(m, [dict(steps=[dict(at_ms=0, event='publish', fields=dict(data=[1]*4096))])], reference=False)
                rc, stdout, _ = rows[0]; self.assertNotEqual(rc, 0)
                observed = [json.loads(s) for s in stdout.splitlines()]
                self.assertEqual(observed[-1]['snapshot'], observed[0]['snapshot'])
                self.assertIn(failure, stdout)

    def test_conflicting_guards_are_all_checked(self):
        m = model(); e = long_value({'var': 'x'})
        m['transitions'][1]['guard'] = op('eq', e, e)
        duplicate = copy.deepcopy(m['transitions'][1]); duplicate['id'] = 'CONFLICT'
        m['transitions'].append(duplicate)
        rows = self.check_models(m, [dict(steps=[dict(at_ms=0, event='clear')])], reference=False)
        self.assertNotEqual(rows[0][0], 0); self.assertIn('rule_conflict', rows[0][1])

    def test_event_field_slots_and_types_remain_distinct(self):
        m = model(); m['events']['scalar'] = dict(origin='application', fields=dict(data='int'))
        e = long_value({'event': 'data'})
        m['transitions'].append(dict(id='SCALAR', **{'from':'READY','to':'READY'}, event='scalar', guard=True,
                                     actions=[dict(emit=dict(message='number', fields=dict(a=e, b=e)))], requirements=['MB']))
        self.check_models(m, [dict(steps=[dict(at_ms=0, event='publish', fields=dict(data=[0, 128, 255])), dict(at_ms=1, event='scalar', fields=dict(data=13))])])

    def test_state_only_helper_in_invariant_and_byte_helpers(self):
        m = model(); e = long_value({'var': 'x'})
        m['invariants'].append(dict(id='nonnegative', requirements=['MB'], **{'assert':op('ge', e, 0)}))
        m['transitions'][1]['actions'] = [dict(emit=dict(message='number', fields=dict(a=e, b=e)))]
        b = op('bytes_slice', op('bytes_concat', {'event':'data'}, {'bytes':[0, 255, 128]}), 0, 8)
        m['transitions'][0]['actions'] = [dict(set=dict(var='buffer', value=b)), dict(emit=dict(message='delivered', fields=dict(data=b)))]
        self.check_models(m, [dict(steps=[dict(at_ms=0, event='publish', fields=dict(data=[1, 2])), dict(at_ms=1, event='clear')])])
        self.assertIn('static inline Bytes shared_expr_', render(m))

    def test_conditional_timer_actions_keep_order_and_skip_errors(self):
        m = model(); delay = long_value(7)
        m['timers']['alarm'] = dict(event='alarm')
        m['events']['alarm'] = dict(origin='timer', fields={})
        bad = long_value(op('add', (1 << 63)-1, 1))
        m['transitions'][1]['actions'] = [
            dict(arm_if=dict(timer='alarm', delay_ms=bad, when=False)),
            dict(arm_if=dict(timer='alarm', delay_ms=delay, when=True)),
            dict(cancel_if=dict(timer='alarm', when=False)),
        ]
        m['transitions'].append(dict(id='ALARM', **{'from':'READY','to':'READY'}, event='alarm', guard=True,
                                     actions=[dict(set=dict(var='x', value=delay))], requirements=['MB']))
        self.check_models(m, [dict(steps=[dict(at_ms=0, event='clear'), dict(at_ms=7, tick=True)])])

    def test_readable_strings_preserve_all_utf8_bytes_and_c99_trigraphs(self):
        value = 'quotes" slash\\ nul\0' + ''.join(chr(i) for i in range(1, 128)) + '中文??/n??=09'
        raw = value.encode()
        source = '#include <string.h>\nint main(void) { const unsigned char expected[]={' + ','.join(map(str, raw)) + '}; const char actual[]=' + cstr(value) + '; return sizeof(actual)!=sizeof(expected)+1 || memcmp(actual,expected,sizeof(expected)); }\n'
        with tempfile.TemporaryDirectory() as tmp:
            c = Path(tmp)/'strings.c'; c.write_text(source); exe = c.with_suffix('')
            subprocess.run(['cc', '-std=c99', '-trigraphs', '-Wall', '-Wextra', '-Werror', str(c), '-o', str(exe)], check=True, capture_output=True)
            self.assertEqual(subprocess.run([str(exe)]).returncode, 0)
