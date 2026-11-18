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

## Counted native text input (v6)

The current `direct-c99-typed-text-v6` lowering keeps shared expressions and adds
string event fields through `u:<UTF-8-hex>` transport. The empty string is `u:`.
A string's meaning is its Unicode scalar content, including embedded NUL; JSON
spelling, byte count and intern ID are not interchangeable. Input rejects
malformed hex, overlong/truncated UTF-8, surrogates and values above U+10FFFF.

A model with string event fields owns a text pool inside its native Machine.
Each entry holds at most 4096 UTF-8 bytes and there are at most 64 distinct entries,
including all source literals. Lookup precedes the capacity check, so existing
values still work in a full pool. The pool is append-only during a process, an
explicit finite native execution domain rather than a restriction on Lean's
universal strings. Pool exhaustion rejects the command without eviction or
truncation. Counted JSON emission preserves NUL and control characters.

The whole candidate Machine, including the owned pool, is copied transactionally.
Parse, invariant and output-capacity failures discard all candidate text/state,
emissions and trace. There is no heap allocation, global mutable text pool or
protocol callback. Source-literal IDs and dynamic IDs deduplicate by exact bytes;
set/eq/ne/ite keep the existing IR meaning. Initial overrides use the same counted
transport. Models without string event fields retain their closed-literal input
interface. Legacy wire codecs remain explicitly unsupported.

Generation binds `text_runtime.c` when used and the command encoder source.
Reports name v6; old evidence still requires its original pinned checker.
Tests exercise unchanged six-step Typed Cell literals, Unicode/NUL/quotes,
4096-byte boundaries, malformed input, full-pool dedup, initial overrides,
source/dynamic equality and state/pool/output rollback. These are concrete native
checks, not a universal compiler or memory-safety proof.
