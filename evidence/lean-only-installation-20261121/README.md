# Verification from the Lean-only installation

A wheel built from the Lean-only framework was installed into a separate Python
environment. Its metadata declared zero Python dependencies. Installed module
bytes match the reviewed source. Z3 and the retired solver backend were absent.

The installed CLI checked the IPv4 closeout using Lean for 335 firings and
18 conflict groups. All 77 reference and generated C comparisons passed.
The explorer covered 10 of 335 rules, retaining the overall unresolved verdict.
The retained verifier checked 1048 output artifacts.

The first installed suite passed 154 tests and failed one extraction provenance
check for the updated rational-clock test. The provenance record was corrected
and that test passed against the same installed wheel. Both original logs are
retained. The source suite also passed with expected Lean-tool skips.

The manifest binds the selected original reports and test logs.
