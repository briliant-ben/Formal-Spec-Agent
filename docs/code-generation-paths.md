# Code generation and Lean correspondence

Z3 does not generate our C. The declarative Protocol IR is lowered by the direct
C99 generator; Z3 checks declared model properties. Lean is an additional proof
checker and can also compile executable Lean definitions to C.

| Route | Current purpose | Runtime / guarantee |
|---|---|---|
| IR → direct C99 generator → C | Standalone subject implementation | No Python or Lean runtime; existing reference/Z3/native evidence |
| IR + actual C → typed semantic views → Lean | Per-output expression translation validation | Checked pure expression correspondence under explicit runtime/ABI contracts |
| IR → Lean interpreter → Lean compiler → C | Optional compiled reference execution | Lean runtime required; matching literals do not prove the native compiler |

Lean's kernel checks proof terms. It does not automatically prove Lean's native
compiler or the C compiler correct. See the official [compilation pipeline](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/)
and [FFI/runtime ABI](https://lean-lang.org/doc/reference/latest/Run-Time-Code/Foreign-Function-Interface/).

## First per-output translation-validation unit

`examples/lean-c-read` selects the first integer assignment in one IR rule.
Supported IR expressions are signed64 literals, booleans, typed event fields,
byte reads and typed conditionals. Slice/concat, arithmetic, state variables,
ordered writes, failure/rollback and scheduling are explicitly outside this
correspondence fragment. The earlier range-only Lean unit remains available.

The checker reads the actual C artifact, checks its pinned runtime prefix and
harness suffix, locates the selected native action and parses its first assignment.
The task also pins the C parser itself, so a grammar change requires a newly
approved task. It accepts only the corresponding pure expression grammar. Shared expression
helpers must be exactly one return expression with unchanged arguments; their
bodies are expanded, never trusted by name. Unknown calls, altered helpers,
macros, line splicing, C99 trigraphs, noncanonical/octal numbers, wrong field types,
cycles and excessive expansion are rejected. The checker never compiles or
executes the provided C artifact. Other function bodies and statements are not
certified; callers still need the independent build/execution pipeline.

The IR tree and parsed C tree are independently reified into typed Lean data.
The frozen obligations check:

- The mathematical C read-helper contract agrees with IR default-zero lookup.
- A nonnegative index below the length is within the natural-index bounds.
- The formal lowering preserves value semantics for every expression in the fragment.
- The parsed artifact tree equals that formal lowering, and its value refines IR
  on native-admissible contexts.
- A nonzero literal context satisfies the native preconditions, and five independent
  literal value contracts hold. A contradictory admission predicate cannot pass
  merely by making the native-domain implication vacuous.

The C model is a mathematical value semantics, **not a formal C implementation
semantics**. Buffer layout, initialized storage, valid pointers, signed/unsigned
ABI interpretation, helper implementation correctness and the C toolchain remain
trusted. Native contexts require buffers ≤4096 bytes, signed64 integer fields and
boolean fields represented by0/1. The generic value model is total outside that
domain; this does not extend the native contract. Full-byte runtime/harness hashes
bind the contract to the actual source profile, but hashes are not runtime proofs.
The strict parser/reifier and JSON-IR-to-Lean adapter are also trusted. The
current `c_expression_model_refinement_checked` flag is deliberately narrower
than compiler, memory, whole-EFSM or protocol correctness.

## Commands

```sh
TASK_SHA=$(shasum -a 256 examples/lean-c-read/task.json | cut -d ' ' -f 1)
formal-spec-agent lean-check examples/lean-c-read/task.json \
  --workspace examples/lean-c-read --proofs examples/lean-c-read/proofs.json \
  --task-sha256 "$TASK_SHA" --lean /path/to/lean-4.35.0/bin/lean \
  --out /tmp/c-read-check-001
formal-spec-agent lean-native examples/lean-c-read/task.json \
  --workspace examples/lean-c-read --proofs examples/lean-c-read/proofs.json \
  --task-sha256 "$TASK_SHA" --lean /path/to/lean-4.35.0/bin/lean \
  --out /tmp/lean-native-reference-001
```

`lean-native` first checks the frozen certificate in a fresh project. It then
uses the same toolchain's Lean compiler and `leanc` driver on trusted reconstructed
Lean definitions and a small runner. Only frozen inputs are compiled into the
runner. Expected values are compared after the process exits. The provided C
artifact and the worker's proof code are **not** compiled into that executable.
Lean's runtime is linked into the result (it may be statically included); this
is different from generating runtime-free C99 source. Generated C, actual
compiler logs, executable hash, observations and proof records
are retained in the fresh output. This reference route is not a replacement for
the standalone C99 endpoint and does not generate a complete TCP/IP stack.

Fresh `lean-verify` reconstructs the approved typed trees and proofs using the
current pinned checker. Code-artifact changes require a new task approval. Even
if a wrong index's C/task/statement hashes are deliberately rebound, its tree
cannot equal the unchanged IR lowering, so the kernel check must fail. Do not
weaken that obligation or refresh expected values to make a mutant pass.
