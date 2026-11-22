# Typed actions and explicitly scheduled microsteps

The shared `TypedMachine.lean` interpreter extends the five-kind pure expression
layer with typed assignment, heterogeneous messages, positive timer arming,
cancellation, unique guard dispatch, source/target state changes and final-invariant
failure. The authoritative protocol remains JSON IR. The adapter derives all
rules, actions, invariants, schemas and timer-event bindings; no protocol callback
or host network stack supplies decisions.

## Ordering and observation contracts

All enabled guards are evaluated on the source snapshot. Zero enabled rules yield
`uncovered`; multiple enabled rules yield `conflict`, without rule priorities. A
firing timer is still active during this selection and removed before actions.
Actions read the current tentative store and timer membership; emits append in
order, and all fields of one message use that same position's store. Target state
is installed only after all actions. Invalid timer delays or final invariants
return an error. `rollback` preserves the complete original snapshot on error;
no tentative message or clock change escapes.

Timers are numbered by lexicographically sorted names, independently of JSON
declaration order. ID0 is an ordinary timer, not a sentinel. Arming replaces the
same timer and requires a positive mathematical integer delay. `stepTimer` chooses
the earliest `(deadline,name)` and requires its exact deadline. The guard sees the
active firing timer; its actions do not, unless they explicitly rearm it.

`external` is an **explicitly scheduled microstep**: every timer due at or before
its time must already have been processed. Otherwise it returns `pendingTimer`.
This differs from the public Python `Machine.dispatch`/`tick` batch API, which
advances timers automatically and rolls back the entire batch on failure. The
Lean adapter rejects backward time and timer-event injection. This milestone does
not claim batch scheduling or batch rollback equivalence. No arbitrary scheduler
fuel or silent truncation is introduced. Rational/clock/post-target and conditional
action semantics remain explicitly outside this adapter.

`MachineObserve.lean` projects every schema variable, all timer deadlines,
selected rule/event, emitted typed fields and error rollback. Sorting is total
structural insertion, so literal checking does not depend on opaque runtime-only
sorting. There is no buffer-length projection:4096 complete bytes and Unicode,
newline and NUL survive both the observer and compiled runtime.

## Separate acceptance claims

`fsa-lean-machine-task-v1` pins sources/model/semantic definitions/adapter and the
exact generated propositions. `lean-check` and fresh `lean-verify` return
`checked_scheduled_microstep_contract`, not `checked_efsm_contract`. The benchmark
has29 kernel obligations: four generic semantic lemmas, seven admitted initial
snapshots and18 frozen operations, including negative cases. The generic
`fire_invariant` lemma establishes successful final-invariant filtering; it does
**not** establish that each enabled rule preserves invariants before that filter.
It must not substitute for an all-rule preservation obligation.

```sh
TASK_SHA=$(shasum -a256 examples/lean-machine/task.json | cut -d ' ' -f1)
formal-spec-agent lean-check examples/lean-machine/task.json \
  --workspace examples/lean-machine --proofs examples/lean-machine/proofs.json \
  --task-sha256 "$TASK_SHA" --lean /path/to/lean --out /tmp/machine-check-001
formal-spec-agent lean-verify /tmp/machine-check-001 \
  --task examples/lean-machine/task.json --workspace examples/lean-machine \
  --task-sha256 "$TASK_SHA" --lean /path/to/lean --out /tmp/machine-recheck-001
```

`lean-machine-run` independently compiles an input-only interpreter and runner
through Lean to C. It links Lean's runtime; it is not standalone protocol C99 or
a verified native compiler. Its builder cannot accept expected outputs. All
observations are compared after process exit against frozen literals; definitions,
compiler identities, original stdout and source/executable hashes are retained.
`kernel_literal_contract_checked` and whole-EFSM/protocol/compiler proof flags
remain false for this execution result, even when its values match.

```sh
MODEL_SHA=$(shasum -a256 examples/lean-machine/model.json | cut -d ' ' -f1)
CASES_SHA=$(shasum -a256 examples/lean-machine/cases.json | cut -d ' ' -f1)
formal-spec-agent lean-machine-run examples/lean-machine/model.json \
  --workspace examples/lean-machine --cases examples/lean-machine/cases.json \
  --model-sha256 "$MODEL_SHA" --cases-sha256 "$CASES_SHA" \
  --lean /path/to/lean --out /tmp/machine-runtime-001
```

The complete pinned TCPIP case's335 rules and all four action kinds are reified
and compiled. A nine-transition pre-existing native/reference fixture matches the
Lean runtime's entire store/timers/outputs. Its provenance file binds unchanged
source literals; it is not an independent RFC oracle or a new network run. This
execution check does not prove reachability, all-rule safety, compiler correctness
or English/RFC interpretation. Historical UNKNOWNs remain under their original
checkers. The maintained complete timed flow, all-rule preservation and case
integration are documented in [timed contracts](lean-timed-contracts.md).
