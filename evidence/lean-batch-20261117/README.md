# Typed total batch scheduler checkpoint

Functional source: `0ad56a26a19f387cce193fce656b77fa796653a5`.
Source plus the user's parent PR merge: `766c3e722e803c303422bf8cdb8063ac985573aa`.
The parent merge has no functional tree change. This evidence does not certify
all original task obligations or retirement of Z3.

Actual local verification with official Lean 4.35.0:

- 158 full methods passed, including the real kernel and pinned compact TCPIP
  microstep regressions. All five new gate methods passed.
- An independently built and installed base wheel, with Z3 actually absent,
  passed 86 Lean methods and two dependency-isolation methods.
- The installed public `lean-batch-run` compiled and ran all 22 batch operations,
  comparing complete fields, snapshots, timers, time, outputs and errors after
  subject exit. The result leaves all full-certificate/safety/compiler/protocol
  proof flags false. Lean-generated C requires the Lean runtime.
- The generic minimum/action/timer progress theorems and total scheduler compile.
  Fifteen separate semantic/replay axiom audits contain only the existing
  approved Lean foundational axioms; no progress assumption or fuel limit.
- The new generic `BatchReplay.sound` theorem connects proved selector/step
  equations to the same total well-founded scheduler. Unit mutation checking
  confirms that the kernel rejects a leaked successful prefix after failure.
- The independent standalone C retained 22 exact unit operation-prefix results;
  these are not a continuous live peer or new network observations.

The original 31 proposition bodies remain byte-identical. The development task
adds 22 stronger internal-result equalities, not assumptions. Its monolithic
proof attempt remains **resource UNKNOWN**, retained with the original source,
logs and proof data. Generic core success and runtime matches do not promote
those failures. Connecting the new replay bridge to the literal proof generator,
universal typed preservation/coverage and full-flow migration remain work.

`raw-evidence.tar.gz` retains installed runtime source/C/native output, separate
kernel axiom audit, independent C unit output, development failures, terminal
provider status receipts, tests and immutable Git source bindings. The manifest
binds every original member. Read-only review rehashed every archive member and
checked 22 installed input/source bindings against Git, all 15 axiom reports,
the unchanged 31 propositions and actual result flags. It did not execute
archived Python, native code or Lean. The failed provider requests are terminal
and were not retried. Build attempts blocked by unavailable build dependencies
and restricted network are retained; the subsequent wheel build/install passed.

See [semantics and pending gates](../../docs/lean-batch-scheduling.md).
