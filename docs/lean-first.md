# Lean-first migration

The target is one Lean-centered acceptance path driven by Protocol IR. Providers
propose proof data; actual kernel checking and a separate axiom audit decide
acceptance. Changing a prover does not transfer old guarantees to a new backend.

## Installation

`pip install .` installs no solver. The Lean expression, C-expression, state-action
and compiled-reference paths work in that installation. Install official Lean
4.35.0 separately, not an unrelated Python package named `lean`. CI uses two
independent environments: the base package with Z3 actually absent, and
`pip install '.[z3]'` for all existing regressions. `requirements-formal.txt`
remains an alternative for the optional backend.

Old versions of the ten-stage `run` task still request Z3 work. Without that extra
they explicitly block their formal stage, never skipping it or falling back to
Lean. New [task-v6](lean-efsm-flow.md) explicitly runs the full flow with Lean for
the admitted timer-free integer EFSM fragment. Scoped Lean callers can also use
`lean-check`, `lean-verify` and `lean-native`. Reference
execution and C99 generation also work without importing Z3. Some internal code
uses solver-free hashing/replay definitions in `symbolic.py`; Z3 itself is loaded
only for a requested solver operation.

## Gates before retiring the optional backend

| Capability | Lean coverage | Remaining work |
|---|---|---|
| Pure expressions | Five types and all26 compact-case operators reified; complete case expression typing, 56 values and3 generic properties | Typed transition connection and broader proof automation; not universal interpreter equivalence |
| Generated C correspondence | Independently parsed pure expression under runtime/ABI contracts | Ordered C statements, native failure and memory contracts |
| IR state effects | Five types, all compact-case expressions, ordered set/emit/arm/cancel, target states and final-invariant rollback | Universal before-filter preservation and native arithmetic/memory correspondence |
| EFSM validity | All-rule preservation, pairwise overlap, complete state/event coverage, initial validity and enabling witnesses in the integer fragment | Broader types/operators, reachability, temporal properties and an interpreter/dispatcher connection |
| Time | Typed single steps plus kernel-checked total batch progress/scheduler and replay bridge; 22 compiled batch operations match frozen literals | 57-obligation batch literal certificate accepted; broader clocks, universal typed rule checking and full-flow adaptation remain |
| Test generation | Existing literal/exploration/native tests | Lean-backed witness/coverage generation and replay |
| End-to-end flow | Explicit task-v6 Lean formal stage, complete snapshots, all ten stages and honest retained/fresh checks | Broader IR semantics and TCP/IP adaptation |
| TCP/IP case | Existing model/C/demo and historical evidence | Pin the validated framework, regenerate and recheck covered claims |

Retire Z3 code only after every supported task has a Lean replacement or an
explicitly reviewed retirement. Preserve old evidence and UNKNOWNs under their
original checkers. Never delete an unmet obligation or promote an expression
certificate to whole-protocol correctness.

## Ordered action-block unit

`examples/lean-state/model.json` supplies the actions and every invariant. The
trusted adapter emits typed Lean data. It accepts integer literal/state/event
expressions, set, one-integer emit, equality, ordering and binary conjunction.
It requires atomic-v1, a single-state true-guard application self-loop and no
timers. Other semantics are rejected. Indices are bounded by the model schema.
Mathematical integers are used; there is no native overflow theorem.

`StateSubset.work` reads from the current tentative store and appends emissions
in order. `execute` checks all final invariants, committing the full candidate
or returning original values with no emissions. Generic obligations check failure
rollback, successful invariant checks and read-after-write. Four frozen literal
witnesses also require initially admitted states, successful delivery and rejected
negative/over-bound inputs. Contradictory admission and reversed set/emit mutants
fail actual Lean checking even after rebinding hashes.

This unit starts after rule selection. It does not prove a rule enabled, unique,
reachable or live, or certify actual C statements. Independent reference/C runs
check the frozen examples, not universal translation correctness. The IR adapter,
semantic definitions, toolchain and specification interpretation remain trusted.
The status is `checked_state_contract`, with C-expression refinement and compiler
correctness flags false. New checker epochs require fresh evidence; old evidence
is preserved under its original version.

[Total batch scheduling](lean-batch-scheduling.md) describes the checked generic
termination/replay core and accepted 57-obligation literal certificate, while
preserving the earlier unresolved attempts.
