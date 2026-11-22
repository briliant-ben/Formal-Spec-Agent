# Typed values for the compact IPv4 case

`TypedIR.lean` now represents the five value types and 26 expression operators
used by the pinned TCPIP-Model case. Expressions are typed data derived from the
authoritative IR, not protocol-specific Python callbacks. The mathematical
evaluator includes full-byte reads/slices/concatenation, modulo byte packing,
Internet checksum arithmetic, sequence arithmetic/comparisons, typed equality,
conditionals, Boolean/integer operations, and pure state/timer-membership queries.
Timers here are only membership queries; scheduling and effects are not proved.

The reifier validates kind/arity/version and field slots before emitting typed
Lean constructors. Variables and fields use their declared global slot and kind;
cross-event sharing is valid only for structurally equal typed field references.
Unsupported operators, rational/clock semantics and malformed values are refused.
Unicode scalar strings include newline/NUL; lone surrogates are explicitly outside
this Lean string domain. Exact run factoring preserves all bytes of large
literals. There is no byte-length projection, magnitude clipping or fixed fold
fuel. The complete derived view includes initializers and all guard, action-value
and invariant expressions. Root-to-node metadata retains rule/requirement IDs.

## Distinct acceptance claims

`lean-types` compiles the entire shared expression view. Its result is
`typed_ir_view_checked`, with `efsm_safety_proved=false`. This establishes that
the derived view typechecks, not the adapter's correctness, a full dispatcher,
invariants, reachability, timer behavior or the protocol specification. The
335-rule case is not yet accepted by the integer-only EFSM contract backend.

```sh
formal-spec-agent lean-types /case/model.json --workspace /case \
  --model-sha256 APPROVED_MODEL_SHA --lean /path/to/lean-4.35.0/bin/lean \
  --out /tmp/typed-view-001
```

The `fsa-lean-typed-expression-task-v1` contract additionally binds literal
contexts, expected values, semantic definitions and adapter. Every model operator
must occur in the selected targets' syntax footprints; this is not an execution
coverage theorem for every branch. The benchmark supplies a direct target for
each of the 26 operators, with alternative and boundary cases. Its 59 actual
kernel obligations are 56 independent literal values and three generic properties:
checksum range, sequence-distance range and half-space unordered behavior.
This is not universal equivalence to a reference interpreter or native compiler.
Types are not promoted into the separate `checked_efsm_contract` result.

## Arithmetic choices and sources

Checksum pairing, odd-byte padding, end-around carry and complement follow the
arithmetic described in [RFC1071 §1](https://www.rfc-editor.org/rfc/rfc1071.html#section-1).
The recursion is total and kernel-checked, with a proved result bound; it does not
apply UDP absent-checksum or zero-to-FFFF policy. Those decisions remain in IR.

[RFC9293 §3.4](https://www.rfc-editor.org/rfc/rfc9293.html#section-3.4) requires
modulo2^32 sequence arithmetic. The existing IR defines sequence addition for
arbitrary signed mathematical offsets. This is a totalization, not a claim that
all offsets are defined under [RFC1982 §3.1](https://www.rfc-editor.org/rfc/rfc1982.html#section-3.1).
At the half-space difference, the IR's comparable/lt/le values are false;
[RFC1982 §3.2](https://www.rfc-editor.org/rfc/rfc1982.html#section-3.2) leaves the
ordering undefined. Callers must not infer an RFC ordering from that false value.

## Compiled reference and independent checks

`lean-native` now also accepts typed-expression tasks. It first checks the
certificate, then reconstructs an input-only `ModelValues.lean` and runner in a
separate runtime directory. It never imports the task's propositions or worker
proofs into that program. The builder's input schema cannot contain expected
outputs. Expected values are compared only after the process exits. Text results
are serialized as scalar codepoints so newline/NUL cannot disappear in parsing.
The original certificate remains intact and can still be freshly rechecked.
The earlier C-expression native route now preserves that separation too.

The executable links Lean's runtime. It is a mathematical reference, not the
standalone protocol implementation. Independent Python IR evaluation checks all
frozen values; independent standalone generated C checks the benchmark's default
29-result operation. Actual compiled Lean execution includes 1500/4096-byte data,
negative packing, wrap/half-space and Unicode/NUL. Native compiler correctness
remains trusted rather than proved.

The typed proof profile fixes recursion capacity at16384; command deadlines stay
unchanged. Resource errors are retained as `resource_unknown`, never false proofs
or success. A 4096-byte proof exceeded that fixed capacity and was preserved;
exact length/append lemmas repaired the proof without increasing limits, shrinking
the data, changing expected output or approximating the checksum. Restricted
`rewrite`, `attempt` and `simp_only` instructions cannot bypass kernel acceptance.

Existing Z3 results/UNKNOWNs remain under their original checkers. The later
[timed endpoint contracts](lean-timed-contracts.md) cover typed effects, timers
and all-rule model invariant preservation. C compiler correctness and broader
protocol behavior remain separate obligations.
