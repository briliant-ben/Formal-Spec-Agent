# Lean-first installation and state-action acceptance

Functional source: `3b55f8228061275ab99a1abb9e21ac06020a725f`.
Actual local execution: official Lean 4.35.0, Python 3.12, macOS arm64.
This is not Linux networking or a new TCP/IP execution.

- 109 source tests passed with the actual Lean checker required.
- An independent installed base package with Z3 actually absent passed 37 Lean
  tests and 2 installation/import tests from an unrelated directory. This includes
  actual compiled Lean reference C, not only a mocked tool.
- Fresh public CLI state check and fresh recheck accepted eleven goals and the
  separate axiom audit: `checked_state_contract`. C/compiler/protocol proof flags
  remain false. Frozen inputs and source epochs were rechecked after execution.
- Four independently fixed generated C/reference/literal cases matched. Native
  rejection leaves variables, output and transition trace uncommitted.
- Fresh public `lean-native` in that solver-free installation returned
  `[65,0,0,0,255]` with the linked Lean runtime. Compiler correctness is not proved.
- An actual old mailbox flow without Z3 reported `blocked/environment` for its
  formal stage; reference/native comparison still passed. No fallback or UNKNOWN
  promotion occurred.

`raw-evidence.tar.gz` retains 247 original files, each listed in `manifest.json`.
It includes Lean source/kernel/axiom logs, executable/compiler evidence, native
literal observations, blocked old-flow records, proposal/review inputs/receipts,
original proof rejections and test output. All members were rehashed after
archiving. Treat retained code/ELFs as evidence; fresh rechecking uses trusted
current source, not archived execution. Original rejected epochs stay rejected.

See `review-triage.md` for the two paid completed calls, controller proof repairs
and sixteen review labels individually checked against source. The independent
review preceded the final certificate-claim hardening and did not approve the
final source; actual regressions and CI provide that source's validation.

Scope: integer-only, timer-free mathematical IR action blocks. This does not
prove guard selection, reachability, target changes, native overflow, actual C
statements, whole EFSM, scheduling, English specification interpretation or a
complete protocol. The optional Z3 backend and all historical UNKNOWNs remain.
