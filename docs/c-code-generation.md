# Compact C generation

The `direct-c99-shared-expressions-v5` backend emits standalone C99 from the
same admitted IR fragment as v4. Protocol policy stays in IR. The reference
interpreter, Z3 encoding, dispatcher and byte runtime are unchanged.

The generator counts exact lowered compound expressions, including their result
type, and extracts repeated expressions of at least 80 source characters into
model-derived typed functions. Helpers receive the current machine and event
fields and run at the original expression position. They do not cache values,
precompute conditional branches, reorder assignments or remove guard checks.
All eligible guards are still evaluated to detect rule conflicts. Children are
defined before parents in a deterministic order; state-only helpers do not need
event pointers. This is source factoring, not algebraic simplification.

Printable ASCII uses ordinary C string literals. Quotes, backslashes, question
marks (C99 trigraph safety), control bytes and non-ASCII UTF-8 bytes are escaped.
Three-digit octal escapes prevent following digits from extending an escape.
This reduces source text while preserving the emitted string bytes.

`render(model, share_expressions=False)` is a diagnostic unshared lowering used
for compiled comparisons. Normal generation and evidence rebuilding always use
the shared lowering. Generation reports bind the changed generator and name v5;
old v4 evidence must be checked using its original pinned framework version.
The historical extraction manifest is unchanged. Explicit current source hashes
are recorded separately in `provenance/evolution.json`.

Tests compile both forms and compare complete output, including state changes,
byte expressions, typed event fields, short-circuit conditions, integer overflow,
byte capacity failures, atomic rollback and rule conflicts. Successful examples
also compare with the reference interpreter. These checks are not a universal
compiler-correctness proof. Existing C operand evaluation-order limitations,
4096-byte value buffers, stack use and diagnostic output remain; this change
does not claim an embedded-memory optimization or change supported protocols.
