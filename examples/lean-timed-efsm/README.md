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
