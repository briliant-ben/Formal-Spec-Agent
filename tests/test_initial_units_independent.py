import unittest
from unittest.mock import patch
import z3
from protocol_lab.initial_units import reduce_initial_constants


class IndependentReductionTests(unittest.TestCase):
    def equivalent(self, terms):
        r = reduce_initial_constants(terms)
        self.assertEqual(len(r['assertions']), len(terms))
        self.assertTrue(all(any(z3.eq(b, t) for t in terms) for b in r['bindings']))
        s = z3.Solver()
        s.add(z3.Xor(z3.And(*terms), z3.And(*r['bindings'], *r['assertions'])))
        self.assertEqual(s.check(), z3.unsat)
        return r

    def test_scalar_binding_reconstruction_is_equivalent(self):
        x, inp, post = z3.Ints('v_0_x event_value v_1_x')
        r = self.equivalent([x == 7, inp > 1000000, post == x + inp])
        self.assertEqual(len(r['bindings']), 1)

    def test_sequence_domain_above_MTU_preserved(self):
        seq = z3.SeqSort(z3.BitVecSort(8))
        old, inp = z3.Consts('v_0_buf network_bytes', seq)
        self.equivalent([old == z3.Empty(seq), z3.Length(inp) > 1500,
                         z3.Length(z3.Concat(old, inp)) > 1500])

    def test_nonunit_equalities_are_not_bindings(self):
        x, b = z3.Int('v_0_x'), z3.Bool('condition')
        r = self.equivalent([z3.Implies(b, x == 0), x > -2])
        self.assertEqual(r['bindings'], [])

    def test_nonliteral_sequence_and_poststate_are_not_bindings(self):
        seq = z3.SeqSort(z3.BitVecSort(8))
        old, inp = z3.Consts('v_0_buf network_bytes', seq)
        post = z3.Int('v_1_x')
        r = self.equivalent([old == z3.Concat(inp, inp), post == 4])
        self.assertEqual(r['bindings'], [])

    def test_conflicting_units_remain_contradictory(self):
        b = z3.Bool('active_0_t')
        r = self.equivalent([b, z3.Not(b)])
        self.assertEqual(r['bindings'], [])

    def test_no_solver_is_called_by_reducer(self):
        x = z3.Int('now_0')
        with patch.object(z3.Solver, 'check', side_effect=AssertionError('solver called')):
            r = reduce_initial_constants([x == 0, x >= 0])
        self.assertEqual(len(r['assertions']), 2)

    def test_custom_context_bool_units_reconstruct(self):
        ctx = z3.Context()
        b = z3.Bool('active_0_t', ctx=ctx)
        r = reduce_initial_constants([z3.Not(b)])
        self.assertEqual(r['assertions'][0].ctx, ctx)
        self.assertTrue(z3.is_true(r['assertions'][0]))
