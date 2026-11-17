# Worker proposal and rejected development records

DeepSeek0238 returned a source proposal (2507 reported tokens). Controller review
and real Lean found invalid Std proofs/tactics, missing termination reasoning and
an incorrectly parenthesized sequence-distance expression. The final shared
arithmetic was repaired: subtraction precedes modulo; negative packing uses
Euclidean modulo; checksum folding has a kernel-checked decreasing recursion and
an inductive range proof. No checksum truncation or fixed folding fuel is used.
The original proposal, usage receipt and compiler diagnostic remain in `agents/`
and `logs/`; they are not represented as a passing independent implementation.

Independent review request0239 did not complete at the provider. Its original
terminal receipt and sanitized traceback are preserved. It was not automatically
retried, and no independent AI approval/findings are claimed. The API ledger was
not replaced or reset. There are no active paid jobs for this milestone.

Preserved development outcomes include:

- Early checksum proofs could not reduce well-founded recursion with `decide`;
  another draft referenced a Mathlib induction name absent from Std. Both failed.
- Initial native runner compilation failed because its imported module lacked
  an `.olean`. The final separate runtime generates both Lean object and C files;
  the original certificate is no longer polluted by runtime outputs.
- A stale task/adapter epoch was correctly rejected, without weakening its hash.
- The 4096-byte witness exceeded the fixed recursion capacity of16384. This
  remains `resource_unknown`, with native execution blocked. Exact List length
  and append lemmas resolved a later, separately approved proof without raising
  capacity, changing the expected value or shrinking the input.
- Scratch simplification/rewrite failures remain diagnostics, not proofs.

Development bundles retain original generated Lean/logs/result hashes, but do not
all retain every intermediate Python checker blob; do not revalidate them with
current code or present them as fully reconstructable final certificates.
Final immutable source and fresh accepted outputs are separately bound and audited.
