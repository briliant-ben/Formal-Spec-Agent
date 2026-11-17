# Ordered typed scheduled microsteps

## Contract

This generic benchmark fixes five value types, typed ordered assignment/emission,
positive timer delays, unique guard selection, exact-deadline timer firing and
final-invariant failure rollback. Timer ties use lexicographic names; declaration
order is deliberately reversed. A firing timer is active for guard selection and
removed before actions. The state remains the source until actions finish.

External microsteps require all due timers to have been explicitly processed.
This is not the automatic batched dispatch/tick API: pending timers yield an
explicit pendingTimer result. No modeled protocol, scheduler fuel, native integer
overflow theorem, interpreter refinement or compiler proof is claimed.

Expected literals were written independently before running the candidate.
The large buffer retains4096 exact bytes and text includes Unicode/newline/NUL.
Errors preserve the entire caller snapshot and expose no emissions.
