# Ordered integer transaction

The IR is authoritative: assign x from input, emit x, copy current x to y, emit y.
Final bounds constrain both variables. Rejection commits neither writes nor
emissions. Independent `spec.md` fixes four outcomes before proof proposals.
Restricted proof data must pass actual Lean and an axiom audit.
See [scope and migration](../../docs/lean-first.md).

```sh
pip install /path/to/Formal-Spec-Agent
TASK_SHA=$(shasum -a 256 task.json | cut -d ' ' -f 1)
formal-spec-agent lean-check task.json --workspace . --proofs proofs.json \
  --task-sha256 "$TASK_SHA" --lean /path/to/lean-4.35.0/bin/lean \
  --out /tmp/state-check-001
formal-spec-agent lean-verify /tmp/state-check-001 --task task.json --workspace . \
  --task-sha256 "$TASK_SHA" --lean /path/to/lean-4.35.0/bin/lean \
  --out /tmp/state-recheck-001
```

No Z3 installation is needed. This is an action-block contract, not a whole EFSM,
C-statement or protocol proof. Timers and byte operations are explicitly refused
by this unit; earlier pure byte/C units remain available.
