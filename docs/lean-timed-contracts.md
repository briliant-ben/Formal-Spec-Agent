# Raw firing and scheduled preservation

This checkpoint connects actual timer removal and selection to the typed raw
candidate semantics. It does not yet certify a concrete timed EFSM universally.

TypedFiringContracts.FiringPreserves generalizes the timer-free raw property
with an explicit optional fired timer. It quantifies over all typed stores and
fields and requires successful raw work plus every resulting invariant. The
none case is proved equivalent to the older property. Clock independence is
proved from the actual current expression context; it is not an assumption or
permission to accept older clock/rational IR semantics.

The actual fired timer is removed before ordered actions. An independent
counterexample keeps an active-timer invariant: a rule that does not rearm loses
that invariant on firing, even though the filtering runtime rejects the result.
The raw preservation property rejects that model. A positive literal checks
rearm against the current firing clock.

ScheduledPreservation.MatchingRaw collects the raw property for every matching
rule, with the actual optional fired timer. Its checked bridges invert actual
enabled selection, use the raw witness to construct runRule success, and unify
the result with actual fire. External execution uses the real eligibility,
time and pending-timer tests. Timer execution uses actual earliest selection and
its membership lemma. Invariant filtering is not substituted for a raw proof.

These are conditional generic theorems. A concrete owner must still prove raw
preservation, guard disjointness, external and active-timer coverage, declared
timer-ID well-formedness and the repeated batch composition obligations. Those
premises are not automatically assumed true by a task flag. The new timed task
adapter and universal timed-model certificate remain pending.

## Independently frozen Timed Cell

[The benchmark](../examples/lean-timed-efsm) freezes the source and ten stimuli
before model execution. It exercises acceptance, oversize rejection without
refresh, expiry before an external event at the same deadline, refresh from 31
to 35, a no-due tick, full bytes/Unicode/NUL and final backward-time rollback.

Reference execution and one persistent generated-C process match all 10 operations
and 9 transition rows, including the declared final error. A wrong reject refresh
passes the model invariants but fails the frozen oracle; a native timer comparison
fault also fails it. Native reply snapshots do not expose the clock directly:
transition times, deadlines and subsequent backward-time behavior are checked.
There is no live network or compiler/memory proof in this benchmark.

The original DeepSeek oracle incorrectly accepted 17 bytes and refreshed a timer;
that result was rejected. Its completed repair fixes the behavior. Six dispatch
headers were structurally unwrapped, with all values unchanged. Direct code-point
inspection confirms the original and repaired NUL labels were already correct;
display escaping was not a string fault. Original proposals and triage remain.

The model proposal needed explicit source repairs: a true constant constructor,
removal of unsupported duration metadata and arm placement after the five ordered
assignments. The actual delay remains an IR action. Typed machine admission now
rejects unknown timer keys rather than silently projecting them away. The older
microstep task has a fresh adapter approval hash; its proposition source is
byte-identical. Historical evidence requires its original checker.

Optional Z3 and historical UNKNOWNs are retained. No entire timed protocol,
TCPIP case, reachability, C compiler or English specification proof is claimed.


## Exact observation types

A synthetic observation mutation of a genuine native trace exposed an oracle
weakness: Python equality treated JSON Boolean true as integer 1. This was not
a new Linux run or an observed implementation fault. Both native Difference
channels now compare JSON scalar types recursively, keeping object key order
irrelevant and array order/content exact. Integer/float timestamp aliases and
Boolean/numeric state/message aliases fail. Reference scenario final variable
expectations must also match the declared IR type; unknown fields are rejected.
Generation evidence binds the new generic equality helper. No protocol rule,
input, invariant or frozen expected value changes.
