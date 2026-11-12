"""Unit tests for prestate_reduce.reduce_initial_constants."""

import unittest

import z3
from z3 import (
    Bool,
    BoolVal,
    BitVec,
    BitVecVal,
    Int,
    IntVal,
    Not,
    And,
    Or,
    Implies,
    String,
    StringVal,
    Unit,
    Empty,
    Concat,
    Solver,
    sat,
    unsat,
    BitVecSort,
    SeqSort,
    BoolSort,
    IntSort,
    StringSort,
    Const,
)

from protocol_lab.initial_units import reduce_initial_constants


class TestReduceInitialConstants(unittest.TestCase):
    def test_forward_literal_equality(self):
        state_0 = Bool("state_0")
        v_0_x = Bool("v_0_x")
        assertions = [
            state_0 == BoolVal(True),
            v_0_x,
        ]
        result = reduce_initial_constants(assertions)
        self.assertEqual(len(result["assertions"]), 2)
        # Assertion 0 becomes True after substitution and simplification
        self.assertTrue(z3.is_true(result["assertions"][0]))
        # Assertion 1 remains unchanged (v_0_x is a prestate constant but not bound)
        self.assertTrue(z3.is_true(result["assertions"][1]))
        # bindings contains the original equality
        self.assertEqual(len(result["bindings"]), 2)
        self.assertTrue(result["bindings"][0].eq(assertions[0]))

    def test_reverse_literal_equality(self):
        now_0 = Int("now_0")
        v_0_flag = Bool("v_0_flag")
        assertions = [
            IntVal(42) == now_0,
            v_0_flag,
        ]
        result = reduce_initial_constants(assertions)
        self.assertEqual(len(result["assertions"]), 2)
        # First assertion becomes True
        self.assertTrue(z3.is_true(result["assertions"][0]))
        # Second unchanged
        self.assertTrue(z3.is_true(result["assertions"][1]))

    def test_boolean_units(self):
        active_0_main = Bool("active_0_main")
        due_0_timer = Bool("due_0_timer")
        other = Bool("other")
        assertions = [
            Not(active_0_main),  # binds to False
            due_0_timer,         # binds to True
            other,
        ]
        result = reduce_initial_constants(assertions)
        self.assertEqual(len(result["assertions"]), 3)
        # First becomes True after substituting active_0_main=False and simplifying Not(False)=True
        self.assertTrue(z3.is_true(result["assertions"][0]))
        # Second becomes True after substituting due_0_timer=True
        self.assertTrue(z3.is_true(result["assertions"][1]))
        # Third unchanged (other is not allowed prestate constant)
        self.assertTrue(result["assertions"][2].eq(other))

    def test_contradictory_bindings_preserved(self):
        state_0 = Bool("state_0")
        assertions = [
            state_0 == BoolVal(True),
            state_0 == BoolVal(False),
        ]
        result = reduce_initial_constants(assertions)
        # Should return original assertions unchanged and empty bindings
        self.assertEqual(len(result["assertions"]), 2)
        self.assertTrue(result["assertions"][0].eq(assertions[0]))
        self.assertTrue(result["assertions"][1].eq(assertions[1]))
        self.assertEqual(result["bindings"], [])

    def test_unbound_prestate_not_frozen(self):
        v_0_x = Bool("v_0_x")
        other = Bool("other")
        assertions = [
            Or(v_0_x, other),
            other,
        ]
        result = reduce_initial_constants(assertions)
        # No bindings, return unchanged
        self.assertEqual(len(result["assertions"]), 2)
        self.assertTrue(result["assertions"][0].eq(assertions[0]))
        self.assertTrue(result["assertions"][1].eq(other))
        self.assertEqual(result["bindings"], [])

    def test_poststate_untouched(self):
        state_1 = Bool("state_1")
        v_0_x = Bool("v_0_x")
        assertions = [
            v_0_x == BoolVal(True),
            state_1,
        ]
        result = reduce_initial_constants(assertions)
        self.assertEqual(len(result["assertions"]), 2)
        # First substituted
        self.assertTrue(z3.is_true(result["assertions"][0]))
        # state_1 is not allowed prestate, so unchanged
        self.assertTrue(result["assertions"][1].eq(state_1))

    def test_byte_input_untouched(self):
        # A variable starting with v_1_ or other prefix should not be touched
        v_1_byte = BitVec("v_1_byte", 8)
        v_0_x = Bool("v_0_x")
        assertions = [
            v_0_x == BoolVal(True),
            v_1_byte == BitVecVal(5, 8),
        ]
        result = reduce_initial_constants(assertions)
        self.assertEqual(len(result["assertions"]), 2)
        # First substituted
        self.assertTrue(z3.is_true(result["assertions"][0]))
        # Second unchanged
        self.assertTrue(result["assertions"][1].eq(z3.simplify(assertions[1])))

    def test_expression_rhs_not_used(self):
        state_0 = Bool("state_0")
        v_0_x = Bool("v_0_x")
        # RHS is an expression involving another prestate constant, not a literal ground value
        expr = Or(v_0_x, BoolVal(True))
        assertions = [
            state_0 == expr,
        ]
        result = reduce_initial_constants(assertions)
        # Should not bind, assertions unchanged
        self.assertEqual(len(result["assertions"]), 1)
        self.assertTrue(result["assertions"][0].eq(assertions[0]))
        self.assertEqual(result["bindings"], [])

    def test_sat_preserved(self):
        # Simple satisfiable set: state_0=True, v_0_x=True
        state_0 = Bool("state_0")
        v_0_x = Bool("v_0_x")
        assertions = [
            state_0 == BoolVal(True),
            v_0_x,
        ]
        result = reduce_initial_constants(assertions)
        # After substitution, assertion 0 becomes True, assertion 1 remains v_0_x,
        # so satisfiable (v_0_x can be True)
        s = Solver()
        s.add(*result["assertions"])
        self.assertEqual(s.check(), sat)

    def test_unsat_preserved(self):
        # Unsatisfiable due to contradictory facts after substitution:
        # state_0=True, but also assertion Not(state_0) which becomes Not(True)=False -> unsat
        state_0 = Bool("state_0")
        assertions = [
            state_0 == BoolVal(True),
            Not(state_0),
        ]
        result = reduce_initial_constants(assertions)
        s = Solver()
        s.add(*result["assertions"])
        self.assertEqual(s.check(), unsat)

    def test_large_input_allowed(self):
        # Construct a long assertion list >1500 bytes when serialized? The module doesn't care,
        # but test should pass with a larger set.
        state_0 = Bool("state_0")
        many_assertions = [state_0 == BoolVal(True)]
        # Add 1500 dummy constraints
        for i in range(1500):
            b = Bool(f"dummy_{i}")
            many_assertions.append(b)
        result = reduce_initial_constants(many_assertions)
        self.assertEqual(len(result["assertions"]), 1501)
        # First assertion simplified to True
        self.assertTrue(z3.is_true(result["assertions"][0]))

    def test_literal_bv8_seq_binding(self):
        # Test that a Seq(BV8) literal (via Unit) can be used as RHS for a prestate constant
        bv8 = BitVecSort(8)
        seq_sort = SeqSort(bv8)
        v_0_data = Const("v_0_data", seq_sort)
        unit_expr = Unit(BitVecVal(10, 8))
        assertions = [
            v_0_data == unit_expr,
        ]
        result = reduce_initial_constants(assertions)
        self.assertEqual(len(result["assertions"]), 1)
        # After substitution, v_0_data replaced by Unit(10), equality becomes Unit(10) == Unit(10) -> True
        self.assertTrue(z3.is_true(result["assertions"][0]))

    def test_literal_bv8_seq_binding_with_concat(self):
        # Test Concat of literal seqs
        bv8 = BitVecSort(8)
        seq_sort = SeqSort(bv8)
        v_0_seq = Const("v_0_seq", seq_sort)
        empty = Empty(seq_sort)
        unit1 = Unit(BitVecVal(1, 8))
        unit2 = Unit(BitVecVal(2, 8))
        concat_expr = Concat(unit1, empty, unit2)
        assertions = [
            v_0_seq == concat_expr,
        ]
        result = reduce_initial_constants(assertions)
        self.assertEqual(len(result["assertions"]), 1)
        self.assertTrue(z3.is_true(result["assertions"][0]))

    def test_literal_bv8_seq_empty(self):
        # Empty sequence binding
        bv8 = BitVecSort(8)
        seq_sort = SeqSort(bv8)
        v_0_empty = Const("v_0_empty", seq_sort)
        empty = Empty(seq_sort)
        assertions = [
            v_0_empty == empty,
        ]
        result = reduce_initial_constants(assertions)
        self.assertEqual(len(result["assertions"]), 1)
        self.assertTrue(z3.is_true(result["assertions"][0]))

    def test_nonliteral_seq_rhs_rejected(self):
        # RHS is a seq with a variable inside, must not be a binding
        bv8 = BitVecSort(8)
        seq_sort = SeqSort(bv8)
        v_0_seq = Const("v_0_seq", seq_sort)
        x = BitVec("x", 8)
        unit_with_var = Unit(x)
        assertions = [
            v_0_seq == unit_with_var,
        ]
        result = reduce_initial_constants(assertions)
        # No bindings, unchanged
        self.assertEqual(len(result["assertions"]), 1)
        self.assertTrue(result["assertions"][0].eq(assertions[0]))
        self.assertEqual(result["bindings"], [])

    def test_int_binding_actual_fail(self):
        # This test corresponds to the reported failure: Int(v_0_x)==1 should work
        v_0_x = Int("v_0_x")
        assertions = [
            v_0_x == IntVal(1),
        ]
        result = reduce_initial_constants(assertions)
        self.assertEqual(len(result["assertions"]), 1)
        self.assertTrue(z3.is_true(result["assertions"][0]))

    def test_bv_binding(self):
        v_0_bv = BitVec("v_0_bv", 8)
        assertions = [
            v_0_bv == BitVecVal(5, 8),
        ]
        result = reduce_initial_constants(assertions)
        self.assertEqual(len(result["assertions"]), 1)
        self.assertTrue(z3.is_true(result["assertions"][0]))

    def test_string_binding(self):
        v_0_str = String("v_0_str")
        assertions = [
            v_0_str == StringVal("hello"),
        ]
        result = reduce_initial_constants(assertions)
        self.assertEqual(len(result["assertions"]), 1)
        self.assertTrue(z3.is_true(result["assertions"][0]))

    def test_custom_context_bool(self):
        # Uses a custom Z3 context
        ctx = z3.Context()
        state_0 = Bool("state_0", ctx=ctx)
        v_0_x = Bool("v_0_x", ctx=ctx)
        true_val = BoolVal(True, ctx=ctx)
        assertions = [
            state_0 == true_val,
            v_0_x,
        ]
        result = reduce_initial_constants(assertions)
        self.assertEqual(len(result["assertions"]), 2)
        self.assertTrue(z3.is_true(result["assertions"][0]))
        self.assertTrue(z3.is_true(result["assertions"][1]))

    def test_fake_function_name_rejected(self):
        # Declare a constant with a name like v_0_ but as an interpreted function? Actually,
        # uninterpreted function is fine, but named like v_0_fake with arity >0 should be rejected
        # because is_const returns False.
        f = z3.Function("v_0_fake", IntSort(), IntSort())
        x = Int("x")
        # f(x) is not a constant
        assertions = [
            f(x) == IntVal(2),
        ]
        result = reduce_initial_constants(assertions)
        self.assertEqual(len(result["assertions"]), 1)
        self.assertTrue(result["assertions"][0].eq(assertions[0]))
        self.assertEqual(result["bindings"], [])

    def test_invalid_input_type(self):
        with self.assertRaises(ValueError):
            reduce_initial_constants(5)  # not iterable

    def test_invalid_element_type(self):
        with self.assertRaises(ValueError):
            reduce_initial_constants([IntVal(1)])  # not BoolRef

    def test_equality_with_non_bool_literal_rhs_or_expression(self):
        # RHS is an expression with arithmetic
        v_0_int = Int("v_0_int")
        assertions = [
            v_0_int == IntVal(2) + IntVal(3),
        ]
        result = reduce_initial_constants(assertions)
        self.assertEqual(len(result["assertions"]), 1)
        self.assertTrue(result["assertions"][0].eq(assertions[0]))
        self.assertEqual(result["bindings"], [])

    def test_not_equality_but_or_top_level(self):
        v_0_x = Bool("v_0_x")
        state_0 = Bool("state_0")
        or_expr = Or(v_0_x, state_0)
        assertions = [
            or_expr,
        ]
        result = reduce_initial_constants(assertions)
        # Not a binding pattern, unchanged
        self.assertTrue(result["assertions"][0].eq(or_expr))
        self.assertEqual(result["bindings"], [])


if __name__ == "__main__":
    unittest.main()
