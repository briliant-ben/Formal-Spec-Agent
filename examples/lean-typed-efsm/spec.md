# Typed Cell v1

This is a generic mathematical EFSM benchmark, not an Internet protocol.
One state READY; no timers. Variables in order: buf (bytes) initially [], n
(integer) initially 0, cursor (seq32) initially 0, label (text) initially the
empty string, accepted (boolean) initially false.

The sole external event app.put has fields in order payload (bytes), sequence
(seq32), delta (integer), label (text), allow (boolean). All typed field values
are admitted mathematically: arbitrary finite byte lists, valid 32-bit sequence
values, mathematical integers, text and booleans. Do not add implicit bounds.

PUT.ACCEPT is enabled exactly when allow is true AND payload length <=16. Its
ordered actions store the entire payload in buf, set n to the length of the
updated buf, set cursor to (sequence + delta) modulo 2^32, set label to the
input label, set accepted to true, then emit cell.accept. PUT.REJECT is enabled
exactly when that entire acceptance condition is false. It sets accepted=false,
leaves all other variables unchanged, then emits cell.reject. Both target READY.

Both messages expose the complete resulting five variables as fields buf, n,
cursor, label, accepted. The selected event fields, rule, time, state, variables,
timers and full message contents must be observed. No partial buffer projection.
Invariants are n>=0, n<=16, and n equal to the full stored buf length. There is
no assumption restricting buf content, cursor, label or accepted. Native C's
separate finite integer/memory limits are not universal mathematical guarantees.
