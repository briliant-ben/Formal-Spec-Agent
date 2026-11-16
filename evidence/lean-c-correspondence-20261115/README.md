# Pure IR / C correspondence and compiled Lean reference

Functional source: `8f76f8426f5e5a5b60bd7c5aee8ebb416192ddf6`.
Official Lean 4.35.0, macOS arm64. This is local execution evidence, not Linux
network evidence. GitHub CI separately repeats the installed tests and public CLI.

Actual final results:

- 98 source tests and 98 installed-package tests passed with Lean required.
- Fresh public `lean-check` and `lean-verify`: 11 obligations, separate axiom
  audit, `checked_expression_contract`, `c_expression_model_refinement_checked`.
- Fresh public `lean-native`: generated C, linked Lean runtime and executable
  returned `[65, 0, 0, 0, 255]`, matching the frozen five input/output contracts.
- The existing direct C99 generator was not modified. Its independent generated
  C execution and adverse mutations are covered by the new tests.

`manifest.json` binds 178 original files in `raw-evidence.tar.gz`. The archive
includes exact checked Lean sources, proof data, axiom/kernel/compiler logs,
generated reference C, executable, test logs and rejected proposals/diagnostics.
Every archive member was rehashed after creation. Inspect archived code as data;
use fresh current tools to recheck certificates, rather than executing archives.
The archive's source epoch and prior rejected proof epochs remain distinct.

This proves the declared pure mathematical expression correspondence, with the
strict C parser and runtime/ABI contracts trusted. It is not memory, C compiler,
whole-EFSM, scheduling, failure/rollback or full TCP/IP correctness. The native
reference's matching observations do not prove Lean's compiler correct. See
`docs/code-generation-paths.md` for scope and reproducible commands, and
`review-triage.md` for model proposals and controller repairs.
