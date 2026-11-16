# Independent roles and acceptance disposition

Four server requests used the original shared ledger, without resetting it:

| Job | Actual outcome |
|---|---|
| 0234 implementation | Provider request did not complete. Terminal, no automatic retry. No candidate code accepted; usage unavailable in this job's receipt. |
| 0235 independent tests | Completed, 18,034 known tokens. Controller inspected before execution and corrected guessed APIs/statement names. Its deleted-rule test was replaced: it had tried to count a proof-name mismatch as coverage failure. The final test supplies every remaining proof and locates the actual Lean error in the false empty-group coverage theorem. Original proposal retained. |
| 0236 proofs | Completed, 8,470 known tokens. Returned raw tactic strings instead of allowed proof-data objects; restricted renderer rejected before Lean. Controller independently built ordinary restricted unfold/simplify/omega data for the frozen obligations. Actual kernel accepted all 25, without changing statements, witnesses or semantics. Original rejection retained. |
| 0237 independent review | Completed, 18,030 known tokens; no concrete blocking finding. Advisory only; actual source review, regressions and kernel decide acceptance. |

Successful receipts total 44,534 known tokens; the failed call is not silently
omitted from request accounting, nor assigned an invented token amount. There
were no GPT subagents. Source implementation after the failed provider request
was performed by the controller, not attributed to DeepSeek.

The review checked model/base pins, state/event coverage grouping, reversed ge
arguments, concrete witness validation, certificate type selection, command order,
unresolved prefixes, framework snapshots and formal-stage mapping. Its findings
explicitly report no concrete counterexample. Controller cross-checked each:
the current model has six preservation, two overlap, four coverage, six enabling,
six literal and one initial goal; every empty state/event group still produces
an obligation. The same-model binding and complete framework snapshot are tested.
Source/bundle hashes, proof text and type flags are reconstructed from trusted
current source. Retained inspection is integrity-only, not proof of authenticity.

Actual faults exercised by regressions include illegal poststates before runtime
filtering, conflicting guards, false initial admission, wrong literal outputs,
missing coverage, changed source bindings, missing Lean and a forced checker
timeout. The timeout remains nonpassing; attempts to promote it are rejected.
Independent reference and generated C validate the frozen six-step exact-output
seed separately from the universal mathematical rule contracts.

The accepted scope is the timer-free integer fragment. Timers, richer values and
operators, reachability/liveness, interpreter/dispatcher correspondence, native
memory/overflow/compiler and specification interpretation remain unproved. No
old Z3 UNKNOWN, protocol evidence or TCP/IP model is upgraded by this milestone.
