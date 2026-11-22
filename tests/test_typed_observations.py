"""A generated implementation cannot replace JSON Boolean values by integers."""
import copy
from pathlib import Path
import unittest

from protocol_lab.ir import load,ModelError
from protocol_lab.pipeline.worker import reference_case,compare_case
from protocol_lab.codegen.execute import compare
from protocol_lab.flow import run_scenario
from protocol_lab.json_values import same_value

ROOT=Path(__file__).resolve().parents[1]


class TypedObservationTests(unittest.TestCase):
    def setUp(self):
        self.model=load(ROOT/'examples/lean-typed-efsm/model.json')
        self.scenario=dict(scenario_version='0.2',id='typed-observation',initial={},
            steps=[dict(at_ms=0,event='app.put',fields=dict(payload=[0,128,255,7],
                sequence=4294967295,delta=1,label='开\n\0',allow=True))],
            expect=dict(state='READY',timers={},variables={'accepted':True}))
        self.reference=reference_case(self.model,self.scenario)
        self.rows=[dict(status='ready',snapshot=self.reference['initial'])]
        self.rows += [dict(status='transition',**row)for row in self.reference['trace']]
        self.rows.append(dict(status='ok',snapshot=self.reference['final']))

    def test_both_difference_channels_reject_bool_numeric_and_timestamp_aliases(self):
        self.assertEqual(compare_case(self.reference,self.rows,0,False)['status'],'pass')
        self.assertEqual(compare(self.model,self.scenario,self.rows)['status'],'match')
        for mutation in ['after','emitted','reply','event','time']:
            rows=copy.deepcopy(self.rows)
            if mutation=='after':rows[1]['after']['variables']['accepted']=1
            elif mutation=='emitted':rows[1]['emitted'][0]['fields']['accepted']=1
            elif mutation=='reply':rows[-1]['snapshot']['variables']['accepted']=1
            elif mutation=='event':rows[1]['event']['fields']['allow']=1
            else:rows[1]['time_ms']=0.0
            with self.subTest(mutation=mutation):
                self.assertEqual(compare_case(self.reference,rows,0,False)['status'],'fail')
                self.assertEqual(compare(self.model,self.scenario,rows)['status'],'different')

    def test_final_seed_variable_types_are_checked(self):
        for value in [1,1.0]:
            scenario=copy.deepcopy(self.scenario);scenario['expect']['variables']['accepted']=value
            with self.assertRaisesRegex(ModelError,'field/type'):run_scenario(self.model,scenario)
        scenario=copy.deepcopy(self.scenario);scenario['expect']['variables']['missing']=None
        with self.assertRaisesRegex(ModelError,'field/type'):run_scenario(self.model,scenario)

    def test_maps_ignore_key_order_but_lists_and_scalar_types_are_exact(self):
        self.assertTrue(same_value({'a':[False,1],'b':'\0'}, {'b':'\0','a':[False,1]}))
        self.assertFalse(same_value([False,1],[0,True]))
        self.assertFalse(same_value([1,2],[2,1]))
        self.assertFalse(same_value({'n':1},{'n':1.0}))
