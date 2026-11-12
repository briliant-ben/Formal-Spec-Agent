import unittest
import z3
from protocol_lab.initial_overlap import necessary_literal_clash

class TestNecessaryLiteralClash(unittest.TestCase):

    def setUp(self):
        self.ctx = z3.Context()
        self.solver_ctx = self.ctx

    def _make_solver(self):
        return z3.Solver(ctx=self.ctx)

    def _seq(self, name):
        return z3.Const(name, z3.SeqSort(z3.BitVecSort(8, ctx=self.ctx)))

    def _literal_seq(self, bytes_list):
        """Build a ground sequence literal from a list of integers."""
        if not bytes_list:
            return z3.Empty(z3.SeqSort(z3.BitVecSort(8, ctx=self.ctx)))
        result = z3.Unit(z3.BitVecVal(bytes_list[0], 8, ctx=self.ctx))
        for b in bytes_list[1:]:
            result = z3.Concat(result, z3.Unit(z3.BitVecVal(b, 8, ctx=self.ctx)))
        return result

    def _extract(self, base, offset, length):
        return z3.Extract(base, offset, length)

    def test_simple_contradiction_offset0_14_vs_offset12_8(self):
        base = self._seq('input_0_L.net.frame_frame')
        bytes_a = [0] * 14
        bytes_b = [6] + [0] * 7
        lit_a = self._literal_seq(bytes_a)
        lit_b = self._literal_seq(bytes_b)
        eq1 = self._extract(base, 0, 14) == lit_a
        eq2 = self._extract(base, 12, 8) == lit_b
        leaf = z3.And(eq1, eq2)
        result = necessary_literal_clash(leaf)
        self.assertIsNotNone(result)
        (expr_i, expr_j) = result
        self.assertIn(expr_i, [eq1, eq2])
        self.assertIn(expr_j, [eq1, eq2])
        self.assertFalse(expr_i.eq(expr_j))
        s = self._make_solver()
        s.add(leaf)
        s.add(z3.Not(z3.And(expr_i, expr_j)))
        self.assertEqual(s.check(), z3.unsat)
        s2 = self._make_solver()
        s2.add(expr_i, expr_j)
        self.assertEqual(s2.check(), z3.unsat)

    def test_reverse_equality_orientation(self):
        base = self._seq('b')
        lit_a = self._literal_seq([1, 2, 3, 4, 5])
        lit_b = self._literal_seq([9, 9, 9])
        eq1 = lit_a == self._extract(base, 0, 5)
        eq2 = self._extract(base, 2, 3) == lit_b
        leaf = z3.And(eq1, eq2)
        result = necessary_literal_clash(leaf)
        self.assertIsNotNone(result)

    def test_compatible_overlap_returns_none(self):
        base = self._seq('b')
        lit_full = self._literal_seq([0, 1, 2, 3, 4, 5, 6, 7, 8, 9])
        lit_part = self._literal_seq([5, 6, 7, 8, 9])
        eq1 = self._extract(base, 0, 10) == lit_full
        eq2 = self._extract(base, 5, 5) == lit_part
        leaf = z3.And(eq1, eq2)
        result = necessary_literal_clash(leaf)
        self.assertIsNone(result)

    def test_different_base_returns_none(self):
        base1 = self._seq('b1')
        base2 = self._seq('b2')
        lit1 = self._literal_seq([0, 0, 0])
        lit2 = self._literal_seq([1, 1, 1])
        eq1 = self._extract(base1, 0, 3) == lit1
        eq2 = self._extract(base2, 0, 3) == lit2
        leaf = z3.And(eq1, eq2)
        result = necessary_literal_clash(leaf)
        self.assertIsNone(result)

    def test_nonliteral_offset_or_length_returns_none(self):
        base = self._seq('b')
        lit = self._literal_seq([1, 2, 3])
        off = z3.Int('off', ctx=self.ctx)
        eq1 = self._extract(base, off, 3) == lit
        eq2 = self._extract(base, 0, 3) == self._literal_seq([9, 9, 9])
        leaf = z3.And(eq1, eq2)
        self.assertIsNone(necessary_literal_clash(leaf))
        eq1b = self._extract(base, -1, 3) == lit
        leaf2 = z3.And(eq1b, eq2)
        self.assertIsNone(necessary_literal_clash(leaf2))
        eq1c = self._extract(base, 0, 0) == self._literal_seq([])
        leaf3 = z3.And(eq1c, eq2)
        self.assertIsNone(necessary_literal_clash(leaf3))

    def test_length_mismatch_returns_none(self):
        base = self._seq('b')
        lit_4 = self._literal_seq([1, 2, 3, 4])
        eq1 = self._extract(base, 0, 3) == lit_4
        eq2 = self._extract(base, 1, 4) == self._literal_seq([9, 9, 9, 9])
        leaf = z3.And(eq1, eq2)
        self.assertIsNone(necessary_literal_clash(leaf))

    def test_never_select_or_branch_even_with_clash(self):
        base = self._seq('b')
        inner_leaf = z3.And(self._extract(base, 0, 2) == self._literal_seq([1, 2]), self._extract(base, 1, 1) == self._literal_seq([9]))
        or_expr = z3.Or(inner_leaf, z3.BoolVal(True, ctx=self.ctx))
        result = necessary_literal_clash(or_expr)
        self.assertIsNone(result)

    def test_nonliteral_sequence_expr_ignored(self):
        base = self._seq('b')
        other = self._seq('other')
        eq1 = self._extract(base, 0, 2) == other
        eq2 = self._extract(base, 1, 1) == self._literal_seq([9])
        leaf = z3.And(eq1, eq2)
        self.assertIsNone(necessary_literal_clash(leaf))

    def test_custom_context_supported(self):
        ctx = z3.Context()
        base = z3.Const('b', z3.SeqSort(z3.BitVecSort(8, ctx=ctx)))
        lit1 = z3.Unit(z3.BitVecVal(7, 8, ctx=ctx))
        lit1 = z3.Concat(lit1, z3.Unit(z3.BitVecVal(8, 8, ctx=ctx)))
        lit2 = z3.Unit(z3.BitVecVal(9, 8, ctx=ctx))
        eq1 = z3.Extract(base, 0, 2) == lit1
        eq2 = z3.Extract(base, 1, 1) == lit2
        leaf = z3.And(eq1, eq2)
        result = necessary_literal_clash(leaf)
        self.assertIsNotNone(result)

    def test_whole_base_equality_supported(self):
        base = self._seq('b')
        lit_whole = self._literal_seq([1, 2, 3, 4, 5])
        eq1 = base == lit_whole
        eq2 = self._extract(base, 2, 2) == self._literal_seq([9, 9])
        leaf = z3.And(eq1, eq2)
        result = necessary_literal_clash(leaf)
        self.assertIsNotNone(result)
if __name__ == '__main__':
    unittest.main()
