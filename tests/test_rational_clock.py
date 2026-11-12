import copy
import importlib.util
import unittest

from protocol_lab.ir import CLOCK_SEMANTICS, Machine, ModelError, evaluate, validate, value_ok
from protocol_lab.symbolic import Encoding, check, crosscheck_trace


def model():
    return {'ir_version':'0.3','semantics':CLOCK_SEMANTICS,'protocol':'clock-rational',
        'scope':{'terminal_states':[]},'states':['A','B'],'initial_state':'A',
        'requirements':{'S':{'source':'docs/semantics.md','interpretation':'Exact rational and dispatch clock'}},
        'variables':{'x':{'type':'rational','initial':{'n':0,'d':1}},'seen':{'type':'int','initial':0}},
        'events':{'go':{'origin':'application','fields':{'n':'int'}}},
        'messages':{'sample':{'fields':{'r':'rational','ceil':'int','time':'int'}}},'timers':{},
        'transitions':[{'id':'GO','from':'A','to':'A','event':'go','guard':{'op':'and','args':[{'op':'ge','args':[{'clock_ms':True},5]},{'op':'ge','args':[{'event':'n'},0]}]},
           'actions':[{'set':{'var':'x','value':{'op':'rat_scale','args':[{'op':'rat_add','args':[{'var':'x'},{'op':'rat_from_int','args':[{'event':'n'}]}]},{'rat':[1,8]}]}}},
                      {'set':{'var':'seen','value':{'clock_ms':True}}},
                      {'emit':{'message':'sample','fields':{'r':{'var':'x'},'ceil':{'op':'rat_ceil','args':[{'var':'x'}]},'time':{'clock_ms':True}}}}],
           'target_cases':[{'when':{'op':'ge','args':[{'clock_ms':True},10]},'to':'B'}],'requirements':['S']}],
        'invariants':[{'id':'clock-monotonic','assert':{'op':'le','args':[{'var':'seen'},{'clock_ms':True}]},'requirements':['S']},
                      {'id':'positive','assert':{'op':'rat_le','args':[{'rat':[0,1]},{'var':'x'}]},'requirements':['S']}]}


class RationalClockTests(unittest.TestCase):
    def test_guard_and_actions_read_event_clock_and_values_stay_exact(self):
        m=Machine(model())
        with self.assertRaises(ModelError):m.dispatch('go',{'n':1},4)
        self.assertEqual(m.now_ms,0)
        m.dispatch('go',{'n':1},7);self.assertEqual(m.values['x'],{'n':1,'d':8})
        self.assertEqual(m.trace[-1]['emitted'][0]['fields'],{'r':{'n':1,'d':8},'ceil':1,'time':7})
        m.dispatch('go',{'n':1},11);self.assertEqual(m.values['x'],{'n':9,'d':64});self.assertEqual(m.state,'B')

    def test_canonical_values_and_literals_reject_ambiguity_and_old_versions(self):
        for value in ({'n':True,'d':1},{'n':2,'d':4},{'n':0,'d':2},{'n':1,'d':0},{'n':1,'d':-2},0.5):
            self.assertFalse(value_ok(value,'rational'))
        for version in ('0.1','0.2'):
            m=model();m['ir_version']=version
            with self.assertRaises(ModelError):validate(m)
        m=model();m['semantics']='flat-efsm-atomic-ordered-post-target-v2'
        with self.assertRaisesRegex(ModelError,'Clock requires'):validate(m)
        m=model();m['transitions'][0]['actions'][0]['set']['value']['args'][1]={'var':'x'}
        with self.assertRaisesRegex(ModelError,'literal coefficient'):validate(m)

    def test_negative_abs_scale_and_ceil_are_exact_without_floats(self):
        m=Machine(model())
        expressions=[({'op':'rat_ceil','args':[{'rat':[-7,3]}]},-2),
                     ({'op':'rat_abs','args':[{'rat':[-7,3]}]},{'n':7,'d':3}),
                     ({'op':'rat_sub','args':[{'rat':[1,3]},{'rat':[1,2]}]},{'n':-1,'d':6})]
        for expr,expected in expressions:self.assertEqual(evaluate(expr,m),expected)

    def test_rational_input_and_output_schema_uses_canonical_json_values(self):
        m=model();m['events']['go']['fields']['r']='rational'
        m['transitions'][0]['actions'][0]['set']['value']={'event':'r'}
        runtime=Machine(m);runtime.dispatch('go',{'n':0,'r':{'n':3,'d':7}},7)
        self.assertEqual(runtime.values['x'],{'n':3,'d':7})
        with self.assertRaises(ModelError):runtime.dispatch('go',{'n':0,'r':{'n':6,'d':14}},8)


@unittest.skipUnless(importlib.util.find_spec('z3'),'Z3 required')
class SymbolicRationalClockTests(unittest.TestCase):
    def test_clock_guard_exact_fraction_witness_and_full_trace_replay(self):
        m=Machine(model());m.dispatch('go',{'n':1},7);m.dispatch('go',{'n':1},11)
        result=crosscheck_trace(m.model,m.trace)
        self.assertEqual(result['status'],'match',result.get('reason'))
        self.assertEqual(result['witness']['steps'][1]['after']['variables']['x'],{'n':9,'d':64})
        self.assertEqual(check(model(),depth=2,symbolic_initials=())['status'],'bounded_pass')

    def test_all_rational_ceil_values_and_dispatch_clock_have_independent_queries(self):
        m=model();enc=Encoding(m,1,(),byte_encoding='length',sequence_encoding='modular-int')
        z=enc.z;x=z.Real('arbitrary_rational')
        frame={**enc.frames[0],'values':{**enc.frames[0]['values'],'x':x}}
        ceil=enc.expr({'op':'rat_ceil','args':[{'var':'x'}]},frame,{})
        solver=z.Solver();solver.add(z.Or(ceil<x,ceil>=x+1))
        self.assertEqual(solver.check(),z.unsat)
        enc.solver.add(z.Int('choice_0')==0,enc.frames[1]['now']==7,enc.events[0]['go']['n']==1)
        self.assertEqual(enc.solve(),z.sat)
        self.assertEqual(enc.witness(enc.solver.model())['steps'][0]['after']['variables']['seen'],7)

    def test_backend_rejects_nonrational_witness_instead_of_rounding_it(self):
        enc=Encoding(model(),1,());z=enc.z;x=z.Real('unsupported_irrational')
        solver=z.Solver();solver.add(x*x==2,x>0)
        self.assertEqual(solver.check(),z.sat)
        with self.assertRaisesRegex(ModelError,'Non-rational symbolic witness'):
            enc.concrete(solver.model(),x)
