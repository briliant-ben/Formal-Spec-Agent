# Typed Cell benchmark: frozen source and oracle

This new generic benchmark exercises all five IR value kinds, ordered writes,
full byte-content preservation, accepted/rejected inputs and modular sequence
arithmetic. It is not a TCPIP subgraph or a new network protocol.

`spec.md` is the controller-frozen normative contract. `cases.json` fixes six
operations before the model or adapter implementation. The original DeepSeek
oracle0253 had two issues: an extra stimulus wrapper and a wrong final sequence
result. The controller unwrapped the exact stimulus and corrected only the three
copies of the final cursor from MAX to0, using `(0+2^32) mod2^32=0`. All other
expected data and every input remained unchanged. The rejected original response,
input hashes and exact correction receipt are retained before implementation.
No protocol runtime was used to generate the expected values.

Source SHA256: `c86a9a9144a6cdbb9cae939234c8fed2fe1023b8bf2fcda61219bc775e0c1a4c`.
Frozen case SHA256: `2e6f5a87da2814e50488248590d64c927d913552afe9d81b4bde14ef3f054ace`.

The normalized IR and generic `fsa-lean-typed-efsm-task-v1` adapter now produce
14 actual kernel-checked obligations: initial validity, raw preservation for both
rules, universal guard disjointness and declared-state/event coverage, one valid
context, two positive enabling results and six exact full execution results.
Preservation and coverage quantify over all typed stores and fields; six frozen
inputs are additional witnesses, not a restriction of the safety domain.
Fresh rechecking regenerates the statements and proofs from trusted sources.

The Python reference and compiled Lean mathematical interpreter match all six
operations. The independent standalone C channel now matches all six operations, using
counted UTF-8 transport with explicit native capacity limits. `flow.json` uses
explicit task-v7 to run all ten stages with no Z3, including generated tests,
actual C compilation/execution and retained Difference/traceability checks.
`flow-projection.json` records the seed projection; `cases.json` stays unchanged
and the Lean contract checks its full snapshots. This does not claim timers,
reachability, compiler correctness or TCPIP-wide verification. Maintained
formal workflows run exclusively on Lean 4.35.0 with no Z3 backend.

Run the kernel contract with a separately installed pinned Lean 4.35.0:

```sh
TASK_SHA=$(shasum -a 256 examples/lean-typed-efsm/task.json | cut -d ' ' -f 1)
formal-spec-agent lean-check examples/lean-typed-efsm/task.json \
  --workspace examples/lean-typed-efsm --proofs examples/lean-typed-efsm/proofs.json \
  --task-sha256 "$TASK_SHA" --out /tmp/typed-cell-check
formal-spec-agent lean-verify /tmp/typed-cell-check \
  --task examples/lean-typed-efsm/task.json --workspace examples/lean-typed-efsm \
  --task-sha256 "$TASK_SHA" --out /tmp/typed-cell-recheck
```
