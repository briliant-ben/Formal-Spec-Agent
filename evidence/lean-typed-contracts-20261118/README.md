# Typed EFSM contract checkpoint

Source commit: `bb67ed9fe08aa0c6b0ef1e98a4a93e325fb42787`.
The manifest pins 191 retained files and the exact source/IR/oracle epoch.

Real macOS Lean 4.35.0 accepted all14 typed EFSM obligations and a fresh
regeneration/recheck. Preservation and declared-input coverage quantify over
complete typed stores and fields; the six literal execution goals are separate.
Eight semantic definitions/theorems have audited axioms. All169 repository tests
passed. An independently installed package without Z3 passed eight new tests and
two dependency-isolation tests. Python reference and compiled Lean interpreter
match all six frozen operations.

The archive preserves the original rejected theory/oracle/IR proposals,
controller corrections, provider0255 failure (not retried), malformed0256 proof
proposal, independent0261 review and rejected native-text proposals. Review
advice is not proof. One independent wrong-byte mutant fails after model
reapproval, and the runtime-filter counterexample distinguishes actual raw
preservation from silently discarding a bad write.

Independent standalone C explicitly reports string-event input unsupported and
was not compiled/executed for Typed Cell. There is no full ten-stage typed flow,
timer/reachability/compiler or full TCPIP proof here. Native text support remains
separate work. Original UNKNOWNs and optional Z3 are unchanged.

The archive is historical data. Auditing its hashes does not constitute rerunning
Lean, C or a network experiment; never execute archived programs to inspect it.
