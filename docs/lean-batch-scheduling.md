# Total typed batch scheduling

Protocol IR remains authoritative. `BatchMachine.lean` extends the typed
interpreter to public `dispatch` and `tick`: select the earliest timer by
(deadline, lexical timer identity), run all due timers, advance to the requested
time, then dispatch the external event. An error discards the entire tentative
batch, including earlier timer outputs. Timer injection is rejected before any
advance. No arbitrary iteration limit or fuel assumption replaces scheduling.

## Checked generic core

The Lean kernel checks `TimerMinimum.next_info` against the actual selector,
`TimerEffects.work_summary` against every typed action list and
`TimerProgress.step_progress` against the actual timer step. Positive timer
arming preserves well-timed states. Each successful due step either strictly
advances the clock or decreases the number of timers due now. The lexicographic
measure is `(target - now).toNat, dueNowCount`. `BatchMachine.advanceAux` is a
well-founded definition using this theorem, not a runtime progress assumption.

`BatchReplay.Replay` decomposes an execution into independently checkable selector
and timer-step equations. Its kernel-checked `sound` theorem connects these facts
to the same total scheduler. The public entry-point lemmas retain final invariant
checks and external-event execution as explicit obligations. A failing suffix
cannot expose a successful prefix. This relation is a proof bridge, not another
runtime scheduler, and a candidate intermediate state is never an assumption:
its actual step equation must first be proved.

Both semantic definitions and replay lemmas receive an explicit axiom audit.
Missing audits or dependencies outside the existing approved Lean foundational
axioms are rejected. These claims do not prove preservation before runtime
invariant filtering, protocol correctness or native/compiler correctness.

## Execution and pending certificate integration

`examples/lean-batch` freezes seven contexts and 22 operations, including tied
deadlines, positive rearms, pure clock movement, two kinds of late-batch failure,
4096 complete bytes, Unicode and NUL. The independent Python reference and
generated standalone C match these literals. Compiled Lean batch execution also
matches them; Lean-generated C requires Lean's runtime. The runtime builder
receives inputs only and compares expected outcomes after subject exit.

The development task retains the original 31 observable/generic obligations and
adds 22 stronger full-result equalities for proof reuse. It is **not an accepted
batch certificate**: monolithic literal proof composition has resource UNKNOWNs
under the unchanged 200000-heartbeat and 60-second/module limits. The generic
core proofs and execution matches do not upgrade those UNKNOWNs. The new replay
bridge still needs integration into the literal proof generator.

For input-only compiled execution with a base installation (Z3 absent):

```sh
formal-spec-agent lean-batch-run examples/lean-batch/model.json \
  --workspace examples/lean-batch --cases examples/lean-batch/cases.json \
  --model-sha256 d9361456d237a0f4e59f045cc254aa99c6c2d8ff454bec85c880af2c81459e2c \
  --cases-sha256 1a13b99dee31ddbd71f4d05e6528e378989ec36881eaf4eedcf05d0030084bac \
  --lean /path/to/lean-4.35.0/bin/lean --out /tmp/batch-runtime-001
```

The `batch_reference_match` result explicitly leaves
`kernel_literal_contract_checked`, `efsm_safety_proved`,
`compiler_correctness_proved` and `protocol_correctness_proved` false.

## Remaining migration gates

Finish the decomposed literal certificate, then extend universal typed-rule
preservation, overlap/coverage and witness generation before applying the new
path to the complete TCPIP case. Preserve all historical checker epochs and
UNKNOWNs. Z3 is already absent from the base installation but remains an optional
backend for supported tasks that lack an equivalent accepted Lean path.
