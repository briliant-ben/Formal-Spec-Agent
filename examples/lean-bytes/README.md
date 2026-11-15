# Lean byte-expression example

`spec.md` freezes the interpretation and independent literals. `model.json` is
the sole protocol-behavior authority; `task.json` selects its assignment
expression and pins the exact derived Lean statements. `proofs.json` contains
untrusted proof data which the kernel/audit gate must check, not an acceptance
claim. See [the proof-gate guide](../../docs/lean-proof-gates.md) for commands,
trusted components, statuses and deliberately narrow coverage.

The unit proves a selected pure expression's contracts. It does not prove the
entire EFSM, C implementation, TCP/IP case, or English-specification correctness.
