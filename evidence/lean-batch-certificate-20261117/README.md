# Accepted exact typed batch certificate

Source epoch: `cc8cf16a2f38f90724c5addcbfbee79982797c15`.
The original IR and frozen cases are unchanged; this is a new checker epoch.
It does not promote any earlier failed or resource-UNKNOWN attempt.

Actual official Lean 4.35.0 results:

- 57 obligations accepted, followed by an independent fresh public-CLI kernel
  recheck. Eighteen semantic/replay axiom reports use only the existing approved
  foundational axioms. The old proof-data language and resource limits remain.
- All original 53 proposition bodies are byte-identical. Four extra obligations
  prove exact-content execution for arbitrary typed byte lists of the required
  length, prove the literal's length, and instantiate the original 4096-byte
  cases. This is not a length-only state projection or an assumed poststate.
- The public input-only compiled Lean runtime matches all 22 full outcomes,
  including same-deadline timers, positive rearms, clock movement, whole-batch
  errors, complete event/message fields and 4096 bytes. It requires Lean's
  runtime; its flags explicitly do not claim a literal kernel certificate by
  execution alone, compiler correctness or whole-EFSM/protocol correctness.
- 161 full tests passed. The separately built/installed base wheel, with Z3
  absent, passed 89 Lean methods and two dependency-isolation checks.
- A retained rebound wrong-stored-byte task fails actual kernel checking, despite
  valid hashes and unchanged lengths/invariants; acceptance is not merely hash
  validation or successful runtime invariant filtering.

The checked `advance_expand` equation exposes one actual scheduler step while
keeping well-founded proof objects opaque. Generic store equalities and stronger
byte-content facts avoid repeated large-literal normalization. No timer loop
cutoff, oracle relaxation, input truncation or hidden protocol callback is used.

`raw-evidence.tar.gz` retains 592 original files. The manifest binds every member.
Read-only auditing checked all hashes, 26 immutable Git source/input bindings,
passed status/claim flags, 57 obligations/18 axiom reports, the original 53
propositions and the rejected byte mutant. It did not execute archived Python,
Lean or native binaries. Fresh checking/execution results are retained separately
from the archived development failures.

DeepSeek review0249 returned no findings with explicit limitations; review0250
returned empty finding and limitation lists. All six final files in review0250
match their immutable source hashes. These responses are advice, not proof or a
comprehensive review guarantee. They do not replace kernel/mutation tests.
Design0251 is advisory and partially rejected: the controller rejected forced
TCPIP-subgraph extraction, opaque input-domain callbacks, statement hashes as
behavior oracles, and conflating foundational axioms with unapproved assumptions.
The corrected new TypedContracts source proposal0252 is separate future work.
Three completed review/design requests used 49,652 known tokens, on the original
ledger without resetting counts or retrying old failed/uncertain requests.

Remaining: universal typed-rule preservation **before** runtime invariant
filtering, guard coverage/disjointness and witnesses in the generic typed gate,
then complete TCPIP/full-flow adaptation. No full335-rule safety, native integer/
memory/compiler, English-specification or complete TCP/IP correctness proof is
claimed. Z3 remains an optional backend until all supported tasks have accepted
Lean replacements or an explicit reviewed retirement.
