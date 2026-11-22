# Lean-only formal architecture

All maintained formal workflows run exclusively on Lean 4.35.0 driven by
Protocol IR, with no Z3 dependency or solver fallback. Providers propose proof
or model data; actual kernel checking and a separate axiom audit decide
acceptance. Changing a prover does not transfer old guarantees to a new backend.

## Installation and active checks

Install the Python package with `pip install .` and install official Lean
4.35.0 separately. Current formal tasks use the timer-free Lean contract for
integer or typed EFSMs (v6/v7), or the reviewed timed Lean contract (v8).
C generation and reference execution use the same validated Protocol IR.

Both [the mailbox task](../examples/mailbox/task.json) and
[the Timed Cell flow](../examples/lean-timed-efsm/flow.json) exercise the full
ten-stage timed Lean strategy (`spec-flow-task-v8`) and C pipeline. The
[timed contracts](lean-timed-contracts.md) describe exact initial admission,
all-rule safety, guard disjointness, timer advance and transactional uncovered
dispatch on the pinned TCP/IP case. Test generation and C comparisons keep
independent scopes and verdicts.

## Historical solver tasks

Task schemas v1–v5 are historical. Reproduce their receipts with the
framework revision pinned by their original reports. The
[transition revision](https://github.com/briliant-ben/Formal-Spec-Agent/tree/c5ef8e35fa2ed78c824a54911ec758c7d7782054)
retains the old solver backend. New execution explicitly rejects these task
schemas with migration guidance.

Existing reference execution retains rational arithmetic and the older clock
IR profiles. Their legacy solver proofs remain with the historical framework.
The current formal routes support the documented atomic Lean fragments.
Broader clocks, directed reachability, and full native compiler correctness
have separate proof obligations.

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
