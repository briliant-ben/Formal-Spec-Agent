# Complete Lean-backed integer EFSM flow

Functional source `f93177370bb096f960b7b6346911605cd50c2dff`.
Actual local execution: Python 3.12 / official Lean 4.35.0 / macOS arm64.
This is not Linux network or TCP/IP execution evidence.

- 125 full source tests passed with actual Lean required.
- Independent installed base package: Z3 actually absent; 53 Lean tests and two
  installation/import tests passed from an unrelated directory.
- Fresh installed public CLI: all ten task-v6 stages passed, 25 actual kernel
  obligations and axiom audits accepted, six declared rules covered by generated
  cases, seven reference/native cases and 15 transitions compared successfully.
- An independently authored six-step seed fixes exact scalar outputs, separate
  from generated expectations. Live witnesses do not restrict universal proofs.
- Retained public verification passed without executing archived code; a separate
  fresh public `lean-verify` accepted the 25 obligations again.
- Before archiving, all 45 bound source/workspace inputs were checked byte-for-byte
  against their blobs in the functional Git commit.

`manifest.json` hashes 206 original files in `raw-evidence.tar.gz`: complete flow
and frozen sources, generated C/executable, original native observations, kernel
and axiom logs, fresh recheck, source/no-Z3 test output, original source API
failure, test/proof proposals and independent review receipts. All archive members
were rehashed after creation. Historical failure remains failed. Inspect retained
artifacts as data; fresh checks use current trusted tools, not archived execution.

The proof-data proposal was rejected before Lean; accepted generic proof data
was independently repaired by the controller. The implementation call did not
complete and was not retried. See `review-triage.md` for attribution and receipts.

The accepted contract is all-rule preservation before filtering, pairwise
disjointness, total state/event coverage, initial validity and enabling/literal
contracts for the admitted timer-free integer fragment. It does not certify
interpreter/dispatcher equivalence, richer values, timers, reachability, native
overflow/memory/C compiler, specification interpretation or complete TCP/IP.
Existing optional Z3 tasks/UNKNOWNs and protocol evidence are unchanged.
