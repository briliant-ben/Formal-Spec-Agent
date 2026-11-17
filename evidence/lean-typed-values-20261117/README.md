# Typed Lean values: controller acceptance record

Source: `614bb37e8d0d60bc8927ec2271a992694dcf1b6e`. PR #9 is stacked on #8.
The archive contains 343 original files. A read-only audit checked each member's
SHA256, immutable Git source blobs and 41 final input bindings. It did not execute
archived code, binaries or the prover. See `manifest.json` for individual hashes.

Fresh installed public CLI checks on macOS with official Lean4.35.0:

- `lean-check` and independent `lean-verify`: 59 kernel obligations and axiom audit.
- `lean-native`: 56 frozen values match actual compiled Lean reference execution;
  the executable uses Lean's runtime. Proofs/oracles are excluded from its inputs.
- `lean-types`: the pinned TCPIP case's 335 rules/65 invariants produce 1722 shared
  expression nodes and 3330 roots; all five types and 26 pure operators typecheck.
  Rule/requirement/action bindings remain in the report. This is not EFSM safety.
- Full suite: 139 methods. Separate installed package with no Z3: 67 Lean methods
  plus two dependency-isolation methods. No Lean tests were skipped in these runs.

`final-cli/` contains raw commands, sources, tool/source hashes, logs, certificates,
compiled reference outputs and the complete case expression view. `pinned-case/`
contains the unchanged case model at TCPIP-Model commit
`dda2f02f90229146b017421fade8701c74534308`, SHA256
`7d5a82541ea55cde3ff39b2e1cf883f6c9f942f5dc535a2736e69044d9e154a5`.
`git-source/` retains relevant immutable framework, tests and example inputs.
The other directories are development diagnostics, explicitly **not** accepted
certificates under the final approval epoch. Their original outcomes remain.

Whole-case transitions, scheduling, compiler correctness, Internet-standard
interpretation and end-to-end TCPIP correctness have not been proved. Existing
Z3 and protocol Difference records are unchanged. This milestone does not retire
the optional Z3 backend or claim that expression typing is a whole-case proof.
