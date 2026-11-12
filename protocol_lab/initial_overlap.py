import z3
from typing import Optional, Tuple, List


def necessary_literal_clash(leaf: z3.ExprRef) -> Optional[Tuple[z3.ExprRef, z3.ExprRef]]:
    """Return a pair of original top-level conjuncts that are necessarily
    contradictory because they constrain overlapping byte ranges of the same
    base sequence to different literal bytes.

    This helper inspects a leaf expression of an original overlap query. It
    flattens only top-level conjunctions (And) recursively; it never descends
    into OR, Not, Implies, or any other operator. It recognizes equalities of
    the form:

        seq.extract(base, offset, length) == ground_literal
        ground_literal == seq.extract(base, offset, length)

    where `base` is a sequence expression (Seq of BitVec(8)), `offset` and
    `length` are literal integer expressions, `offset >= 0`, `length > 0`,
    and `ground_literal` is a finite sequence literal built from
    seq.empty, seq.unit of a literal bit-vector byte, and seq.++ with
    length equal to `length`. As a special case, `base == literal` is
    treated as offset 0 and length len(literal).

    The function collects all such literal-bytes assignments to (base,
    offset, length) triples. If it finds two assignments to overlapping
    byte ranges of the same base (identical AST via z3.eq) that differ in at
    least one common byte position, it returns those two original equality
    expressions. Otherwise it returns None.

    The full domain of sequences is unchanged; no bounds are assumed. Only
    the original expressions are returned, never rewritten or truncated
    constraints.
    """

    # Collect top-level conjuncts without descending into OR/Not/etc.
    def flatten_and(expr: z3.ExprRef) -> List[z3.ExprRef]:
        if expr.decl().kind() == z3.Z3_OP_AND:
            out = []
            for child in expr.children():
                out.extend(flatten_and(child))
            return out
        return [expr]

    conjuncts = flatten_and(leaf)

    # Representation of a single literal byte assignment.
    # Each item:
    #   base: z3.ExprRef (the base sequence expression)
    #   offset: int
    #   length: int
    #   literal_bytes: tuple[int] (the bytes of the literal, length entries)
    #   expr: z3.ExprRef (the original equality AST)
    assignments: List[Tuple[z3.ExprRef, int, int, tuple, z3.ExprRef]] = []

    for conj in conjuncts:
        # Recognize equality in either direction.
        if conj.decl().kind() == z3.Z3_OP_EQ:
            left, right = conj.children()
            for lhs, rhs in ((left, right), (right, left)):
                assignment = _try_literal_extract(lhs, rhs)
                if assignment is not None:
                    base, offset, length, literal_bytes = assignment
                    assignments.append((base, offset, length, tuple(literal_bytes), conj))
                    break  # stop after first orientation that matches

    # Look for overlapping assignments with different bytes.
    for i in range(len(assignments)):
        base_i, off_i, len_i, bytes_i, expr_i = assignments[i]
        for j in range(i + 1, len(assignments)):
            base_j, off_j, len_j, bytes_j, expr_j = assignments[j]
            # Same base AST by structural equality (z3.eq via Python `is`
            # can fail after simplification; use sexpr or z3 ast hash? Use
            # z3.ast_equal via `base_i.eq(base_j)`? We'll use
            # z3.simplify equality? Better: use z3.ast_hash + z3.eq? Z3Py
            # ExprRef provides `eq` for AST equality.
            if base_i.eq(base_j):
                # Compute overlap range.
                start = max(off_i, off_j)
                end = min(off_i + len_i, off_j + len_j)
                if start < end:
                    # Check if any byte in overlap differs.
                    for pos in range(start, end):
                        b_i = bytes_i[pos - off_i]
                        b_j = bytes_j[pos - off_j]
                        if b_i != b_j:
                            return (expr_i, expr_j)
    return None


def _try_literal_extract(
    lhs: z3.ExprRef, rhs: z3.ExprRef
) -> Optional[Tuple[z3.ExprRef, int, int, List[int]]]:
    """If lhs is a seq.extract application and rhs is a ground finite sequence
    literal of matching length, return (base, offset, length, literal_bytes).
    Also handles lhs == base (whole sequence equality) by treating it as
    offset 0, length len(literal).
    """
    # Check if lhs is seq.extract
    if lhs.decl().kind() == z3.Z3_OP_SEQ_EXTRACT:
        base, offset_expr, length_expr = lhs.children()
        offset = _literal_int(offset_expr)
        length = _literal_int(length_expr)
        if offset is None or length is None:
            return None
        if offset < 0 or length <= 0:
            return None
        literal_bytes = _ground_seq_literal(rhs)
        if literal_bytes is None:
            return None
        if len(literal_bytes) != length:
            return None
        return (base, offset, length, literal_bytes)

    # Check if lhs is a base sequence and rhs is a literal (whole equality)
    # Only accept if rhs is a literal and length > 0.
    literal_bytes = _ground_seq_literal(rhs)
    if literal_bytes is not None and len(literal_bytes) > 0:
        # Treat as offset 0, length len(literal).
        return (lhs, 0, len(literal_bytes), literal_bytes)

    return None


def _literal_int(expr: z3.ExprRef) -> Optional[int]:
    """Return Python int if expr is a literal integer, else None."""
    if expr.decl().kind() == z3.Z3_OP_ANUM:
        # Z3 numeral
        return expr.as_long()
    return None


def _ground_seq_literal(expr: z3.ExprRef) -> Optional[List[int]]:
    """If expr is a ground finite sequence literal over BitVec(8), return a list
    of its bytes (integers 0-255). Supports seq.empty, seq.unit, and seq.++.
    Returns None if not a literal, if any byte is not a literal bit-vector,
    or if the sequence is not fully concrete.
    """
    kind = expr.decl().kind()
    if kind == z3.Z3_OP_SEQ_EMPTY:
        return []
    if kind == z3.Z3_OP_SEQ_UNIT:
        byte_expr = expr.children()[0]
        byte_val = _literal_bv8(byte_expr)
        if byte_val is None:
            return None
        return [byte_val]
    if kind == z3.Z3_OP_SEQ_CONCAT:
        parts = expr.children()
        out = []
        for p in parts:
            sub = _ground_seq_literal(p)
            if sub is None:
                return None
            out.extend(sub)
        return out
    # Not a recognized literal form
    return None


def _literal_bv8(expr: z3.ExprRef) -> Optional[int]:
    """Return integer value if expr is a literal bit-vector of size 8, else None."""
    if expr.decl().kind() == z3.Z3_OP_BNUM:
        if expr.size() == 8:
            return expr.as_long()
    return None


def necessary_literal_clash_for_tests(leaf: z3.ExprRef):
    """Wrapper for tests to avoid name clash with actual module function."""
    return necessary_literal_clash(leaf)
