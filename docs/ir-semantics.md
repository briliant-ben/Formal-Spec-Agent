# Protocol IR: reader's guide

Protocol IR is the sole behavioral authority. The current interpreter is
[`protocol_lab/ir.py`](../protocol_lab/ir.py); the independent symbolic encoder is
[`protocol_lab/symbolic.py`](../protocol_lab/symbolic.py). This guide introduces
the interface, not a proof that an English specification was encoded correctly.

| Element | Explicit representation |
|---|---|
| States and variables | Named states, typed values and an initial configuration |
| Events and messages | Typed input/output field schemas and origins |
| Rules | Source/target state, event, Boolean guard and ordered actions |
| Timers | Named event bindings with explicit arm/cancel actions and deadlines |
| Invariants | Named predicates with specification requirement references |
| Requirements | Source/version interpretation and scope assumptions |

Actions execute in order; later assignments observe earlier writes. Transitions
commit atomically and rejected inputs do not partially mutate the machine.
Due timers precede an external input at the same time; timer ties have a defined
name ordering. Witness replay checks the actual events/rules/times/outputs and
state, rather than injecting a desired poststate.

Byte values preserve full octet content. `bytes_slice` uses offset and **count**,
clamps negative arguments to zero and clips overrun at the sequence boundary.
`bytes_at_or_zero` returns zero outside bounds; a protocol must separately express
its length guard. Packing operators use their explicit modular semantics, not
implicit field-range validation. Internet checksum arithmetic is a pure operator;
protocol policies such as UDP absent checksums remain in model rules.

Sequence operations have an explicit 32-bit modular domain. Half-space ordering
must not be replaced by ordinary integer order. Reference semantics also support
versioned rational/clock features; each formal/native backend separately admits
or rejects its supported subset. The C backend has declared finite capacities
and checked integer limits; it must not silently truncate buffers or hide an
unsupported construct behind a callback.

Use [the original extracted contract](semantics.md) and the named IR version for
precise definitions. That source was preserved unchanged for provenance, including
its original language and older scoped examples. This English guide does not
rewrite pinned specifications or old evidence. New runs bind the current tool
source, model, task and expected inputs to their own evidence epoch.
