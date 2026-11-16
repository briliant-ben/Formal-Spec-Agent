# IR / actual C expression correspondence

The authoritative `model.json` is lowered by the existing independent C99 backend
into `generated/protocol.c`. `task.json` binds both, the helper profile, the exact
Lean statement draft and five independent value witnesses. `proofs.json` is proof
data; only the actual kernel and separate axiom audit decide acceptance.

See [code generation paths](../../docs/code-generation-paths.md) for commands,
C grammar, native preconditions and trusted components. This unit checks the
selected pure C expression's value model, not C memory or a whole protocol. It
also demonstrates optional Lean → C reference execution, requiring Lean's runtime.
