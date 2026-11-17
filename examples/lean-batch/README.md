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

**The development `task.json` / `proofs.json` is not yet an accepted certificate.**
The original 31 statements are retained, with 22 stronger internal-result
obligations for proof reuse. Monolithic proof composition still reaches resource
UNKNOWN; the replay bridge needs to be connected to these literal proofs.
Execution matches and generic totality do not upgrade that result.

See [batch semantics and commands](../../docs/lean-batch-scheduling.md). Existing
Z3/UNKNOWN evidence, universal before-filter obligations and compiler/protocol
proof boundaries remain unchanged.
