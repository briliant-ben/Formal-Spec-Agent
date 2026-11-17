# Lean-backed EFSM and end-to-end flow

This protocol-independent two-state scalar mailbox is a framework benchmark.
`spec.md`, the six-step exact-output seed and all six rule witnesses were frozen
before proof generation. Protocol decisions are in `model.json`; Lean contains
generic value definitions and a derived typed view, not another mailbox spec.

```sh
pip install /path/to/Formal-Spec-Agent
export FSA_LEAN=/path/to/lean-4.35.0/bin/lean
TASK_SHA=$(shasum -a 256 flow.json | cut -d ' ' -f 1)
formal-spec-agent run flow.json --workspace . --task-sha256 "$TASK_SHA" \
  --out /tmp/lean-mailbox-flow-001
formal-spec-agent verify /tmp/lean-mailbox-flow-001 --workspace . \
  --task-sha256 "$TASK_SHA"
```

No Z3 or model API is needed. `flow.json` selects explicit task-v6/`lean-efsm`.
The formal stage checks 25 frozen obligations: default initial validity, six
universal rule-preservation checks before runtime filtering, two overlap checks,
four total state/event coverage checks, six enabling witnesses and six literal
poststate/output contracts. Universal contexts are mathematical integers, not the
finite witness or exploration values. Empty rule groups still generate coverage
obligations; an admitted state/event with no rule cannot pass.

The remaining stages generate concrete scenarios, execute the independent
reference and generated standalone C, compare traces and bind source clauses.
Six-rule exploration coverage is a finite observation, separate from the Lean
contracts. Missing Lean blocks the formal stage; timeouts remain unresolved.
Retained verification reconstructs trusted sources and checks records without
executing archives. Fresh kernel checking is a separate command:

```sh
CONTRACT_SHA=$(shasum -a 256 task.json | cut -d ' ' -f 1)
formal-spec-agent lean-verify /tmp/lean-mailbox-flow-001/stages/formal/queries \
  --task task.json --workspace . --task-sha256 "$CONTRACT_SHA" \
  --lean "$FSA_LEAN" --out /tmp/lean-mailbox-recheck-001
```

The current EFSM fragment admits state tests, integer literal/variable/field
expressions, comparisons, and/or/not, ordered set and one-integer emissions.
It refuses unsupported operators/types, timers, post-target/clock semantics and
terminal states. It covers all declared rules/invariants/state-event groups.
Rule witnesses establish enabling, not reachability. The adapter, mathematical
semantics, kernel/toolchain and source interpretation remain trusted. There is
no native overflow/memory/compiler, timing, network or full TCP/IP proof.
