# Frozen acceptance contract for total batch scheduling

This is a development checkpoint, **not an accepted Lean batch implementation**.
`model.json` and `spec.md` fix a generic ordered transaction and timer model.
`cases.json` contains seven independently written contexts and22 operations,
including same-deadline order, positive rearms, late pure clock movement, full
rollback after a second timer or external event fails, timer injection and4096
complete bytes with Unicode/newline/NUL.

The existing Python reference and independent generated C match these literals.
Native tests use a fresh process for each operation prefix; this is unit evidence,
not a continuous live peer. The reference additionally checks rollback of clock
and prior trace; C's snapshot format does not itself expose clock.

`TimerRank.lean` defines a well-founded candidate measure and proves its timed-state
characterization. It does not prove that actual transitions decrease that measure.
The total progress theorem and batch scheduler must pass real Lean checking and
axiom/source audits before this example gains a Lean task or execution command.
No arbitrary scheduler cutoff or runtime progress assumption may replace that
proof. Existing Z3/UNKNOWN evidence and whole-rule obligations remain unchanged.
