# Pure byte-expression contract, revision 1

This example qualifies one event-only integer expression in Protocol IR 0.5.
Every octet is in 0..255. `bytes_slice(data, offset, count)` clamps negative
offset/count to zero and clips at the input length. `bytes_at_or_zero(data, i)`
returns the octet at a valid nonnegative index, otherwise zero. `ite` selects
exactly the enabled branch. No arithmetic overflow operation is used here.

The selected expression slices the input, then returns its indexed byte if
`enabled`, and zero otherwise. Its universal result range is 0..255. Frozen
examples require a nonzero valid delivery, negative-index zero, out-of-range
zero, disabled zero and a maximum-octet result. These examples prevent the
range contract alone from accepting an implementation that always returns zero.

These are expression-level guarantees. The Lean unit does not verify transition
enablement, whole-machine scheduling, native C, buffer allocation, network code,
or that an English Internet specification has been formalized correctly.
