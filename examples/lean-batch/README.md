# Frozen acceptance contract for total batch scheduling

`model.json` and `spec.md` fix a generic typed transaction and timer model.
`cases.json` contains seven independently written contexts and 22 operations:
same-deadline order, positive rearms, clock movement, whole-batch rollback after
a second timer or external event fails, injection rejection, and 4096 complete
bytes with Unicode/newline/NUL.

The Python reference, independent generated C and compiled Lean batch runtime
match these literals. C tests use a fresh process per operation prefix; they are
unit evidence, not a continuous live peer. The reference and Lean also observe
clock rollback; the standalone C snapshot does not expose its clock.

The actual Lean kernel checks the generic minimum/effects/progress theorems,
the total well-founded scheduler and its new proof-carrying replay bridge. No
arbitrary cutoff, progress axiom or length-only projection is used.

The kernel certificate now checks all 57 obligations and supports independent
fresh rechecking: the original 31 statements, 22 stronger execution equalities
and four auxiliary byte-content/length facts. The original 53 proposition bodies
remain unchanged. The 4096-byte case is instantiated from a stronger exact-content
lemma covering arbitrary byte values of that length; no bytes are discarded.

The kernel-checked `advance_expand` equation exposes each real scheduler step
without expanding well-founded proof objects. The original proof-data language
and resource limits are unchanged. Earlier monolithic resource UNKNOWNs are
retained, not retroactively promoted. This remains a frozen execution contract,
not universal preservation before runtime invariant filtering or a compiler,
whole-EFSM/protocol correctness proof.

See [batch semantics and commands](../../docs/lean-batch-scheduling.md). Existing
Z3/UNKNOWN evidence, universal before-filter obligations and compiler/protocol
proof boundaries remain unchanged.
