# Timed Cell benchmark

spec.md is the controller-frozen source, cases.json the independently audited
ten-operation literal contract, and model.json the standalone authoritative IR.
All five value kinds, exact content, timer expiry/refresh, same-deadline ordering
and atomic backward-time rejection are exercised.

The specification hash is
75456866515159edabc2998a97585d1bd891a3c694c83d65f7dd8fbb3f12fdb9.
The case hash is
3eefe8ccf5ddaf5940fbf92d3f45ec1caf7b6d605e0c7cd5809851d4f06a9888.

One reference instance and one generated C process match nine successful
operations and one deliberate time error, with nine complete transition rows.
Native snapshots expose data/state/timers; no-trace tick clock is checked only
through later observable timer and backward-time behavior. The source/task
compiler and universal timed model are not proved by those finite observations.

[Raw firing and scheduled bridges](../../docs/lean-timed-contracts.md) explain the
generic kernel-checked foundation and remaining model-specific obligations.
A universal timed-EFSM task/certificate and full flow integration are pending.

The public timed replay certificate binds the original oracle by hash and
checks 21 obligations in Lean 4.35.0: initial validity, exact batch execution
and observations for all ten operations. The clock and every other field in
the expected rollback snapshot are explicit. Run from the repository root
with the pinned `lean` on PATH:

```sh
example=examples/lean-timed-efsm
task_sha=$(shasum -a 256 "$example/task.json" | cut -d ' ' -f 1)
output=$(mktemp -d)
formal-spec-agent lean-check "$example/task.json" \
  --workspace "$example" --proofs "$example/proofs.json" \
  --task-sha256 "$task_sha" --out "$output/checked"
formal-spec-agent lean-verify "$output/checked" --task "$example/task.json" \
  --workspace "$example" --task-sha256 "$task_sha" --out "$output/rechecked"
```

Both commands return `checked_timed_replay` for this finite certificate. The
public task reads the original `cases.json` directly, including the explicit
empty fault trace. Every next command receives the result of rolling back or
committing the previous actual batch. The proof JSON can only supply proofs for
the approved propositions. The commands run without Z3.
