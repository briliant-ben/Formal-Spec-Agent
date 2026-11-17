# DeepSeek proposals and controller triage

0240 completed a source proposal (7425 reported tokens), but omitted required
`findings`/`limitations` keys and was rejected by its frozen response schema. Its
original source/usage/controller/status remain. It was not an approved response,
and the job was not retried. The controller inspected the completed source and
repaired concrete errors: nonexistent import/Std APIs, invalid sequence defaults,
unsupported Repr instances for function stores, keyword identifiers, Bool/Prop
mixing, opaque partial work and invalid proof scripts. The final action evaluator
uses structural recursion and generic kernel-checked lemmas. The original
minimally adapted import/metadata diagnostic is distinguished from final source.

0241 was a new independent source-review task of the tool-validated component,
not a retry of a failed request. It reported no findings (13966 tokens), with
explicit limits: no fresh checker execution, batch scheduling, universal safety,
compiler proof, exhaustive invalid-input enumeration or RFC interpretation review.
Core interpreter, observer and both adapters exactly match the reviewed bytes.
The final test file additionally binds the immutable TCPIP fixture/model hashes;
that later test-only hardening was not part of the AI review. No independent AI
proof or comprehensive approval is claimed. The original shared ledger remains.

Development outcomes remain separate:

- First adapter had duplicate generated names and was rejected by Lean.
- Early literal proof attempts failed to reduce opaque definitions; the second
  check included a4096-byte recursion-limit UNKNOWN under the fixed16384 profile.
- The final observer uses a total structural insertion sort rather than opaque
  runtime-only sorting. Exact length/append lemmas avoid expanding4096 bytes during
  invariant checking. Buffer equality still checks full content. Limits, inputs,
  expected outcomes, guards and invariants were not weakened or shrunk.
- Fifth check passed all29 goals, then unused simplifier arguments were removed
  and fresh installed CLI/kernel checking passed again. The earlier failures and
  UNKNOWN remain original outcomes, not retrospectively successful certificates.

Intermediate bundles retain generated Lean/logs/result hashes; not every older
Python adapter blob was retained at each development instant. Treat those as
original diagnostics, not fully reconstructable certificates under current code.
Final source and fresh accepted checks are completely Git-bound separately.
