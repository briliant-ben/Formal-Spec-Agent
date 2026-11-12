"""Pure planning of initial SMT queries for one-step invariant checking.

This module renders Z3 SMT-LIB strings for the exact original safety and
overlap queries of the symbolic checker, plus a nonvacuity witness query and
per-choice safety reductions. It performs no solving: z3.Solver.check(),
z3.Solver.model(), Python Machine/reference evaluation, and any filesystem or
network I/O are prohibited here.

All solver objects are constructed with z3.Solver(); only `add` and `to_smt2`
are invoked, never `check` or `model`. The intended caller is a trusted
process that serializes these plans and later solves them.
"""

from __future__ import annotations

import ast
import hashlib
import json
from typing import Any, Dict, List, Optional

import z3

from protocol_lab.initial_units import reduce_initial_constants
from protocol_lab.initial_overlap import necessary_literal_clash
from protocol_lab.ir import validate
from protocol_lab.symbolic import Encoding, model_hash

# Plan schema version and required defaults
PLAN_SCHEMA = "initial-step-plan-v1"
PLAN_DEPTH = 1
PLAN_DEFAULT_INITIALS: List[str] = []


def _expr_sexpr(expr: z3.ExprRef) -> str:
    """Return a canonical S-expression string for a Z3 expression."""
    return z3.simplify(expr).sexpr()


def _sexpr_flatten_or(goals: List[z3.ExprRef]) -> List[z3.ExprRef]:
    """Flatten OR goals and drop False leaves from overlap extraction."""
    out: List[z3.ExprRef] = []
    for g in goals:
        if g.decl().kind() == z3.Z3_OP_OR:
            out.extend(_sexpr_flatten_or(list(g.children())))
        else:
            if not (g.decl().kind() == z3.Z3_OP_FALSE):
                out.append(g)
    return out


def _dedup_exprs(exprs: List[z3.ExprRef]) -> List[z3.ExprRef]:
    """Deduplicate exprs by sexpr string, preserving order."""
    seen = set()
    result = []
    for e in exprs:
        key = _expr_sexpr(e)
        if key not in seen:
            seen.add(key)
            result.append(e)
    return result


def render_plan(model: Dict[str, Any]) -> Dict[str, Any]:
    """Render a JSON-serializable plan for one-step invariant checking.

    This function constructs the exact original safety and overlap queries used
    by the symbolic checker at depth 1 with no symbolic initials, then reduces
    per-choice safety queries using the provided constant-elimination helper.
    It also prepares a nonvacuity witness query for the first transition. No
    solver result is obtained; the plan is a pure description of the SMT queries.

    Raises:
        ValueError: if the model is invalid or unsupported for the plan.
    """
    # 1. Validate the model against the real IR.
    validate(model)

    # 2. Check required IR version and semantics.
    if model["ir_version"] != "0.6":
        raise ValueError("Only IR version 0.6 is supported")
    if model["semantics"] != "flat-efsm-atomic-ordered-v1":
        raise ValueError("Only flat-efsm-atomic-ordered-v1 semantics is supported")
    if model["scope"].get("terminal_states"):
        raise ValueError("Terminal states are not supported in this plan")
    if not model["transitions"]:
        raise ValueError("Model must have at least one transition")
    if not model["invariants"]:
        raise ValueError("Model must have at least one invariant")

    # 3. Create the base Encoding exactly as the checker would for depth 1, no
    #    symbolic initials, no fixed choices yet.
    enc = Encoding(model, 1, [], solver_preprocess="none")
    base_assertions = list(enc.solver.assertions())

    # 4. Collect all invariant expressions for both frames, exactly as the
    #    checker: for every frame (enc.frames) and every invariant.
    all_invariants = [
        enc.expr(inv["assert"], frame)
        for frame in enc.frames
        for inv in model["invariants"]
    ]

    # 5. Build original safety goal:
    #    Or(Not(And(all_invariants)), *enc.action_faults)
    safety_or_goals = [z3.Not(z3.And(*all_invariants))]
    safety_or_goals.extend(enc.action_faults)
    original_safety_goal = z3.Or(*safety_or_goals)

    # 6. Build original overlap goal:
    #    Or(*enc.conflicts)
    original_overlap_goal = z3.Or(*enc.conflicts) if enc.conflicts else z3.BoolVal(False, ctx=enc.z.ctx)

    # 7. Serialize original safety and overlap queries including the base.
    def _full_smt(goal: z3.ExprRef) -> str:
        solver = z3.Solver()
        solver.add(*base_assertions)
        solver.add(goal)
        return solver.to_smt2()

    original_safety_smt = _full_smt(original_safety_goal)
    original_overlap_smt = _full_smt(original_overlap_goal)

    # 8. Determine the number of transitions and derive the choice variable.
    transitions = model["transitions"]
    num_choices = len(transitions)
    choice_z3 = z3.Int("choice_0")

    # 9. Build original full safety query with choice unconstrained to use in
    #    reduction via helper.
    original_assertions = base_assertions + [original_safety_goal]

    # 10. Apply constant elimination to original_assertions.
    reduced_result = reduce_initial_constants(original_assertions)
    reduced_assertions = reduced_result["assertions"]
    binding_sources = reduced_result["bindings"]

    # 11. For each valid choice index (including all rule indices, plus -2 for
    #     clock tick and -1 for idle), substitute the choice variable and
    #     serialize. The plan must cover all choices, including idle and clock.
    safety_per_choice = []
    # Valid choices: 0..num_choices-1 (rules), -1 (idle), -2 (clock tick).
    for idx in list(range(num_choices)) + [-1, -2]:
        # Substitute choice_z3 with idx in all reduced assertions.
        substituted = [
            z3.substitute(a, (choice_z3, z3.IntVal(idx)))
            for a in reduced_assertions
        ]
        # Re-add all original binding source constraints to retain complete
        # prestate witness reconstruction, as required by the helper contract.
        final_assertions = substituted + binding_sources + [choice_z3 == idx]
        # Serialize with solver.
        solver = z3.Solver()
        solver.add(*final_assertions)
        smt = solver.to_smt2()
        # Record the choice and SMT string.
        choice_meta = {
            "choice": idx,
            "smt2": smt,
        }
        if idx >= 0:
            choice_meta["rule"] = transitions[idx]["id"]
        else:
            choice_meta["rule"] = None
        safety_per_choice.append(choice_meta)

    # 12. choice_cover field must be an SMT query string, as required by the
    #     actual contract: it must be a string containing the full SMT-LIB
    #     encoding of the disjunction of all valid choices and the safety goal.
    #     We construct a solver with base assertions, original safety goal,
    #     and NOT(choice_0 in {0..num_choices-1, -1, -2}).
    choice_cover_solver = z3.Solver()
    choice_cover_solver.add(*base_assertions)
    choice_cover_solver.add(original_safety_goal)
    # Build OR of equalities for all valid choices.
    valid_choices = [z3.IntVal(i) for i in list(range(num_choices)) + [-1, -2]]
    choice_cover_solver.add(z3.Not(z3.Or([choice_z3 == c for c in valid_choices])))
    choice_cover_smt = choice_cover_solver.to_smt2()

    # 13. Overlap reduction: Reduce original overlap query with helper, then
    #     extract the leaves of the OR goal, deduplicate, and serialize
    #     each leaf standalone with base assertions, without reintroducing
    #     the whole base relation, as required.
    overlap_original_assertions = base_assertions + [original_overlap_goal]
    overlap_reduced_result = reduce_initial_constants(overlap_original_assertions)
    overlap_reduced_assertions = overlap_reduced_result["assertions"]
    overlap_binding_sources = overlap_reduced_result["bindings"]
    # The last assertion is the reduced overlap goal.
    last_assertion = overlap_reduced_assertions[-1]
    # Extract OR leaves.
    overlap_leaves = _sexpr_flatten_or([last_assertion])
    overlap_leaves = _dedup_exprs(overlap_leaves)

    overlap_per_leaf = []
    for leaf in overlap_leaves:
        # Each initialized leaf is a stronger obligation by itself.
        # UNSAT suffices; SAT must be confirmed against original F.
        # Do not reintroduce the whole transition relation here.
        selected = necessary_literal_clash(leaf)
        parts = []
        def conjuncts(expr):
            if z3.is_and(expr):
                for child in expr.children():
                    conjuncts(child)
            else:
                parts.append(expr)
        conjuncts(leaf)
        if selected is not None and (len(selected) != 2 or
                not all(any(item.eq(part) for part in parts) for item in selected)):
            raise ValueError('Overlap reduction invented a constraint')
        # Dropping conjuncts weakens the query: UNSAT of this subset is a
        # stronger obligation. Neither input bytes nor their domain is changed.
        solver = z3.Solver()
        solver.add(*(selected if selected is not None else [leaf]))
        smt = solver.to_smt2()
        overlap_per_leaf.append({
            "index": len(overlap_per_leaf),
            "smt2": smt,
            "derivation": "necessary_literal_conjunct_pair" if selected is not None else "original_leaf",
            "source_leaf_sha256": hashlib.sha256(leaf.sexpr().encode()).hexdigest(),
        })

    # 14. Nonvacuity witness query: fresh Encoding with fixed_choices=[0],
    #     original base only; no reductions, no solving.
    nonvac_enc = Encoding(model, 1, [], fixed_choices=[0], solver_preprocess="none")
    nonvac_solver = z3.Solver()
    nonvac_solver.add(*nonvac_enc.solver.assertions())
    nonvac_smt = nonvac_solver.to_smt2()

    # 15. Compute model semantic hash as in checker.
    model_semantic_hash = model_hash(model)

    # 16. Assemble plan.
    plan = {
        "schema": PLAN_SCHEMA,
        "depth": PLAN_DEPTH,
        "default_initials": PLAN_DEFAULT_INITIALS,
        "model_semantic_sha256": model_semantic_hash,
        "original_safety": {
            "smt2": original_safety_smt,
            "count": 1,
            "slots": ["original"]
        },
        "original_overlap": {
            "smt2": original_overlap_smt,
            "count": 1,
            "slots": ["original"]
        },
        "choice_cover": choice_cover_smt,  # now a string SMT query, not a description
        "safety": safety_per_choice,  # per-choice safety queries, including idle/clock
        "overlap": {
            "leaf_count": len(overlap_leaves),
            "queries": overlap_per_leaf,
            "empty_overlap": len(overlap_leaves) == 0
        },
        "nonvac_smt2": nonvac_smt,
        "counts": {
            "original_safety_queries": 1,
            "original_overlap_queries": 1,
            "per_choice_safety_queries": len(safety_per_choice),
            "overlap_leaf_queries": len(overlap_leaves),
            "nonvac_witness_queries": 1
        },
        "warnings": [
            "The SMT2 strings in this plan are generated in-process; successive checksums may differ due to z3 FreshInt name nondeterminism.",
            "This planner does not solve; it only describes queries."
        ]
    }
    return plan
