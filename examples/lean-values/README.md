# Pure typed operator benchmark

`model.json` owns all behavior. The independently frozen `cases.json` contains
56 exact values covering all 26 compact-case operators plus state/timer queries,
wrap/half-space, odd/checksum-zero, negative packing, Unicode/NUL and long buffers.
The task adds three generic kernel-checked bounds/boundary properties.
See [scope and arithmetic sources](../../docs/lean-typed-values.md).

```sh
TASK_SHA=$(shasum -a 256 task.json | cut -d ' ' -f 1)
formal-spec-agent lean-check task.json --workspace . --proofs proofs.json \
  --task-sha256 "$TASK_SHA" --lean /path/to/lean-4.35.0/bin/lean \
  --out /tmp/typed-values-001
formal-spec-agent lean-native task.json --workspace . --proofs proofs.json \
  --task-sha256 "$TASK_SHA" --lean /path/to/lean-4.35.0/bin/lean \
  --out /tmp/typed-native-001
```

The base package needs no Z3. `checked_typed_expression_contract` checks these
declared values/properties; it is not a whole EFSM or compiler certificate.
Standalone generated C and compiled Lean reference are separate channels.
