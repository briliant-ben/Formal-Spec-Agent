"""Exact prestate constant elimination for full-sequence invariant queries.

This module reduces an SMT assertion set by substituting explicitly bound
prestate constants with their literal ground values, where the bindings are
syntactically present as top-level unit equalities in the original assertion
list. It performs only AST-level substitution and simplification; no solver
queries are issued.

Allowed prestate constant names:
  - state_0
  - now_0
  - any symbol starting with v_0_, active_0_, or due_0_

Allowed literal ground RHS values:
  - bool, int, bit-vector, or string constants
  - finite Seq(BV8) expressions built from Empty/Unit/Concat where Unit and
    Concat carry bit-vector constants

No other functions, variables, or expressions are accepted as RHS. The
substitution is applied to every original assertion via z3.substitute and then
simplified with z3.simplify. All assertion slots are preserved, including any
that simplify to True.

Conflicting bindings (two different RHS values for the same prestate constant)
are detected and cause the original assertion list to be returned unchanged.
"""

from __future__ import annotations

from typing import Dict, Iterable, List, Tuple, Union, Any

import z3
from z3 import (
    BoolRef,
    ExprRef,
    BoolVal,
    IntVal,
    BitVecVal,
    StringVal,
    SeqRef,
    substitute,
    simplify,
    is_true,
    is_false,
    is_eq,
    is_not,
    is_const,
    is_int_value,
    is_bv_value,
    is_string_value,
)

# Allowed prestate constant prefixes and exact names
_ALLOWED_PREFIXES = (
    "v_0_",
    "active_0_",
    "due_0_",
)
_ALLOWED_EXACT_NAMES = {
    "state_0",
    "now_0",
}


def _is_allowed_prestate_constant(expr: ExprRef) -> bool:
    """Return True if expr is a zero-arity uninterpreted constant with an allowed name."""
    if not is_const(expr):
        return False
    # Check that it's an uninterpreted constant (not a defined function)
    if expr.decl().kind() != z3.Z3_OP_UNINTERPRETED:
        return False
    name = str(expr.decl().name())
    if name in _ALLOWED_EXACT_NAMES:
        return True
    return any(name.startswith(prefix) for prefix in _ALLOWED_PREFIXES)


def _is_allowed_literal_ground_value(expr: ExprRef) -> bool:
    """Return True if expr is a literal ground value allowed as substitution RHS."""
    # Literal booleans, integers, bit-vectors, strings
    if is_true(expr) or is_false(expr):
        return True
    if is_int_value(expr):
        return True
    if is_bv_value(expr):
        return True
    if is_string_value(expr):
        return True

    # Finite literal Seq(BV8) built from Empty/Unit/Concat with literal BV8 arguments
    if isinstance(expr.sort(), z3.SeqSortRef):
        # Must be Seq of 8-bit bitvectors
        element_sort = expr.sort().basis()
        if isinstance(element_sort, z3.BitVecSortRef) and element_sort.size() == 8:
            return _is_literal_bv8_seq(expr)
    return False


def _is_literal_bv8_seq(expr: ExprRef) -> bool:
    """Return True if expr is a finite literal Seq(BV8) expression.

    Recognized forms:
      - Empty sequence (SeqEmpty of sort Seq(BV8))
      - Unit(BV8 literal)
      - Concat(literal_seq, literal_seq)
    """
    decl = expr.decl()
    kind = decl.kind()
    if kind == z3.Z3_OP_SEQ_EMPTY:
        return True
    if kind == z3.Z3_OP_SEQ_UNIT:
        arg = expr.arg(0)
        return is_bv_value(arg) and arg.size() == 8
    if kind == z3.Z3_OP_SEQ_CONCAT:
        return all(_is_literal_bv8_seq(a) for a in expr.children())
    return False


def _extract_binding(
    assertion: BoolRef,
) -> Union[Tuple[ExprRef, ExprRef], None]:
    """Try to extract a prestate constant -> literal ground value binding.

    Recognized top-level forms:
      - (= prestate_constant literal_ground_value)
      - (= literal_ground_value prestate_constant)
      - (not prestate_bool_constant)           -> binding to False
      - prestate_bool_constant                 -> binding to True

    Only assertions with no other structure are considered. The assertion must
    be a Z3 BoolRef. If a recognized pattern is found, returns (const, value);
    otherwise returns None.
    """
    # Handle Not(bool_prestate_constant)
    if is_not(assertion):
        arg = assertion.arg(0)
        if _is_allowed_prestate_constant(arg) and arg.sort().kind() == z3.Z3_BOOL_SORT:
            return (arg, BoolVal(False, ctx=arg.ctx))
        return None

    # Handle bare bool_prestate_constant
    if _is_allowed_prestate_constant(assertion) and assertion.sort().kind() == z3.Z3_BOOL_SORT:
        return (assertion, BoolVal(True, ctx=assertion.ctx))

    # Handle equality
    if is_eq(assertion):
        lhs, rhs = assertion.arg(0), assertion.arg(1)
        if _is_allowed_prestate_constant(lhs) and _is_allowed_literal_ground_value(rhs):
            # Ensure rhs is not an allowed prestate constant (to avoid variable-variable binding)
            if _is_allowed_prestate_constant(rhs):
                return None
            return (lhs, rhs)
        if _is_allowed_prestate_constant(rhs) and _is_allowed_literal_ground_value(lhs):
            if _is_allowed_prestate_constant(lhs):
                return None
            return (rhs, lhs)
    return None


def reduce_initial_constants(assertions: Iterable[BoolRef]) -> Dict[str, object]:
    """Eliminate explicitly fixed prestate constants from assertions.

    Args:
        assertions: Iterable of Z3 BoolRefs representing the original
            assertion set F.

    Returns:
        A dict with keys:
            'assertions': list of Z3 BoolRefs after substitution and
                simplification. All original assertion slots are preserved.
            'bindings': list of source expressions (Z3 BoolRefs) that were
                used as bindings. These are the original top-level unit
                assertions that defined a prestate constant.

    If conflicting bindings are detected (same constant bound to different
    literal ground values), the original assertion list is returned unchanged
    with an empty bindings list, and no substitution is performed.

    Raises:
        ValueError: if assertions is not an iterable or contains non-BoolRef
            elements.
    """
    # Validate input type: must be iterable
    try:
        original_list = list(assertions)
    except TypeError as e:
        raise ValueError("assertions must be an iterable of BoolRefs") from e

    # Validate that every element is a BoolRef
    for i, a in enumerate(original_list):
        if not isinstance(a, BoolRef):
            raise ValueError(f"Element at index {i} is not a Z3 BoolRef: {type(a)}")

    bindings: Dict[ExprRef, ExprRef] = {}  # const -> value
    binding_sources: List[BoolRef] = []

    for assertion in original_list:
        extracted = _extract_binding(assertion)
        if extracted is None:
            continue
        var, val = extracted
        # Check for conflicting binding
        if var in bindings:
            if not bindings[var].eq(val):
                # Conflict: return original assertions unchanged, empty bindings
                return {
                    "assertions": original_list,
                    "bindings": [],
                }
            # Duplicate same binding: keep only the first source? We'll still add source for completeness
            binding_sources.append(assertion)
        else:
            bindings[var] = val
            binding_sources.append(assertion)

    # If no bindings, return original list unchanged
    if not bindings:
        return {
            "assertions": original_list,
            "bindings": [],
        }

    # Build substitution list: (var, value)
    substitution_pairs = [(var, val) for var, val in bindings.items()]

    # Apply substitution to every original assertion, then simplify
    reduced_assertions = []
    for assertion in original_list:
        substituted = substitute(assertion, *substitution_pairs)
        simplified = simplify(substituted)
        reduced_assertions.append(simplified)

    return {
        "assertions": reduced_assertions,
        "bindings": binding_sources,
    }
