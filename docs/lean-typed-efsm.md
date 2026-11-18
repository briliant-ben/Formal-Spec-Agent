# Universal typed EFSM contracts

`TypedContracts.lean` defines the obligations needed to extend the older
integer-only universal EFSM gate to all five existing value kinds. Definitions
of obligations do not constitute proofs that an arbitrary model satisfies them.

`candidate` executes the actual ordered `TypedMachine.work`, removes a firing
timer exactly as the existing interpreter does, then sets the target state. It
returns the complete transition without checking final invariants. The checked
`runRule_eq_filter` theorem connects this raw candidate to actual `runRule`.
`RulePreserves` requires an initially invariant-valid, enabled rule to have an
actual successful raw candidate whose final invariants hold. The existential
success requirement prevents vacuity from an action block that always errors.
The checked forward theorem derives actual `runRule` success from raw
preservation; successful runtime filtering is never used to prove preservation.

Guard disjointness quantifies over complete typed stores and event fields.
Coverage quantifies over all declared state IDs and actual external event IDs.
There are no opaque legal-state callbacks, implicit field ranges or byte-length
projections. Positive `Enables` contexts include exact full transition results;
reachability is a separate obligation.

The source proposal0252 omitted external-event membership in coverage and its
first shared-match proof did not compile. The controller restored the already
specified event-domain condition and replaced the proof's one-sided split with
cases on the actual shared work result, changing no theorem statement. Original
source/failure and exact zero-API patch receipts remain retained. Real kernel
checks and axiom audits pass for the corrected theory. A semantic counterexample
shows that an illegal write is filtered at runtime but violates `RulePreserves`.
A mutation restoring the original event-domain omission fails the independent
kernel coverage contract. These are foundation checks, not whole-model proofs.

The generic adapter now admits the timer-free atomic set/emit fragment and
emits one raw preservation goal per IR rule, initial validity, universal guard
disjointness and full declared-state/external-event coverage. Every rule requires
an exact positive enabling witness. Literal cases derive each next prestate from
actual interpreter rollback, never from the expected state. An enabling context
is isolated; its reachability is not implied by its validity.

The independent Typed Cell benchmark exercises all five value kinds, sequential
writes, full byte content, UTF-8/NUL labels and sequence wrapping. Its 14 goals
pass the real Lean kernel and fresh regeneration/recheck with unchanged resource
limits. A same-length wrong-byte model mutation fails the exact contract. Missing
witnesses, incomplete oracle fields, changed source pins and tampered certificate
claims are rejected. The eight semantic definitions/theorems have audited axioms.
No new proof tactic or trusted runtime callback is introduced.

The reference and compiled Lean interpreter match the six frozen operations.
Standalone C now matches the same six unchanged operations with bounded counted
UTF-8 input. Explicit task-v7 integrates this contract with all ten flow stages;
its source snapshot, independent C execution and retained verifier bind the same
whole IR and frozen cases. V6 retains its integer contract and cannot alias V7.
The flow seed is only an exact emission/time projection of the independent
cases; full transition snapshots remain checked by the 14 Lean obligations.
Finite exploration covers both rules and is distinct from universal contracts.
Timers, reachability, native integer/memory/compiler refinement, English
specification correctness and the complete TCPIP case remain separate work. Existing integer task schemas and
historical Z3 results retain their original meanings. Z3 is not retired here.
