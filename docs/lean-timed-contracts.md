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

The batch proof follows the rank of the actual scheduler. For successful
advance, tick and dispatch, it proves that every recorded transition and the
final snapshot satisfy the model invariants and contain only declared timer
IDs. The premises are a valid initial snapshot, well-timed deadlines, a
nondecreasing clock, declared IDs in arm actions, and raw preservation for
each declared trigger. The successful dispatch proof covers both the timer
prefix and the final external event. The proof places no bound on the number
of timer firings.

The domain proof follows actual ordered actions, including cancellation,
replacement of an existing timer and scheduling of a new one. Lean rejects
the static arm obligation for a model that tries to schedule an undeclared ID.
The concrete timed task must still discharge raw rule preservation, guard
disjointness, external and active-timer coverage and its initial timer domain.
The batch preservation theorem is conditional on successful execution.
Separate selection theorems derive success of an eligible external step or a
selected due timer from coverage, disjoint guards, unique rule IDs and raw
preservation. Active-timer coverage uses the timer's actual event and empty
typed field environment. Lean rejects a declared active timer with no rule in
the current state. The batch totality theorem composes these steps using the actual scheduler's
well-founded rank. For an admitted snapshot and a nondecreasing requested
time, advance and tick reach the requested clock with every remaining
deadline strictly in the future. Dispatch additionally requires a declared
external event. It consumes the complete due prefix, executes the event and
returns an admitted snapshot for the next call. The model obligations include
declared rule targets, initial invariants, well-timed deadlines and the
contracts for actual rule selection. The theorem has no scheduler fuel cap.

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

A concrete kernel regression reifies the Timed Cell IR through the existing
batch view. It checks initial validity, declared timer and target IDs, unique
rule IDs, guard disjointness, timer and external coverage, and raw preservation
for all five rules. It then applies the generic dispatch theorem to the
generated initial snapshot with arbitrary typed event fields. The public
timed task certificate and its finite batch replay integration are still open.

The compiled Lean batch interpreter matched the ten original frozen
operations directly. An error expectation can specify the fault, exact
rollback snapshot including the clock, and an empty trace. The older
fault-only form still derives the expected snapshot from the preceding
successful state. These expectations are checked after execution and are
excluded from the runtime source.

## Declared events without enabled rules

Timer completion has its own set of contracts. A model can satisfy these
contracts while exposing an external event for which no guard holds. Once the
actual timer prefix has finished, the dispatcher returns the invariant and
domain checked success result when a rule is enabled. If the enabled list is
empty, it returns the uncovered fault and rollback restores the original
snapshot, discarding the tentative prefix. The proof uses the actual enabled
list at the post-prefix snapshot.

The kernel checks the exact list of eight declared external events with no
rule in the pinned 335-rule TCP/IP model against the reified IR. Each event
returns the uncovered fault from the model's initial snapshot for every
nonnegative request time and arbitrary typed fields. The proof for arbitrary
admitted snapshots with timers requires the separate timer contracts, which
still need to be discharged for TCP/IP. The other thirteen declared external
events have at least one structural match. Their guards and raw actions have
separate proof obligations.
A separate compiled Lean batch replay and the Python reference both rejected
all eight events with the expected empty trace and rollback from the same
initial state. This replay used default typed fields and request times 1 to 8.
The kernel theorem covers arbitrary typed fields and nonnegative times.

## Public timed replay certificates

The [Timed Cell task](../examples/lean-timed-efsm/README.md) uses
`fsa-lean-timed-replay-task-v1` to bind the model, specification and entire
literal oracle as separate files. `lean-plan` derives the propositions,
`lean-check` checks proof data and audits axioms, and `lean-verify` reconstructs
and rechecks a certificate. Failed operations need the explicit fault,
rollback snapshot and an empty trace. A certificate covers its named literal
cases. Universal model and scheduler obligations retain their separate scope.

## Deriving universal obligations from IR

The timed contract renderer derives each raw firing obligation from the
actual rule, external event declarations and timer-to-event bindings. It
groups conflict obligations by source state and event. Lean independently
enumerates the firings and groups from the lowered model and checks equality
with the rendered catalogs. The group proposition quantifies over every two
distinct rule IDs in the group and arbitrary typed input and state values
satisfying the model invariant. A general theorem combines all group proofs
into guard disjointness for the actual dispatcher.

The Timed Cell kernel regression discharges the complete typed timer
contracts and checks the scheduler theorem. It also proves that dropping the
last timer firing or conflict group produces an unequal catalog. On the
pinned TCP/IP model, Lean confirms 335 raw firing entries and 18 conflict
groups. External coverage remains a separate obligation because the TCP/IP
profile admits uncovered inputs.

`GuardDiscriminators` proves that guards cannot both hold when their
conjuncts require incompatible values for the same observation. Lean
checks the meaning of each observation against the typed expression
evaluator. Integer comparisons support equality, inequality and inclusive
bounds, including bounds on byte reads, slice lengths and integer arithmetic.
Negated bounds use exact integer complements.
Text and Boolean equalities use typed state or event slots. Expressions
outside this fragment supply no facts. Pairs the checker cannot separate
remain individual obligations.

Literal byte matches in constant-offset slices yield necessary facts about
the original buffer. The projection theorem requires that the byte is
present in the slice. A nonzero read proves presence because the IR
returns zero outside the slice. Empty slices and zero reads supply no
absolute-byte facts through those respective rules.

Observation keys also retain checksum, concatenation and packing semantics.
A pair with opposite requirements for the same equality is excluded even
when both operands depend on the input. The proof uses equality of the
typed observation keys to bind the two guards to the same computation.

For integer comparisons, moving constant offsets across a relation gives
a checked bound on the difference of its two observations. When a length
expression selects between padding and an unpadded length, the checker
derives a lower bound only if both branches support it. This includes
a length floor that tests and retains the same expression above a
threshold and otherwise uses padding at least as large as that threshold.
Boolean variable and field guards can be compared directly with their
negations while keeping the two slot namespaces separate. A disjunction is
excluded only after accounting for every combination of its alternatives
with those of the other guard.

Sequence operations use the typed 32-bit modular evaluator. Equality
requires zero distance in both directions. Strict ordering gives a
distance in the forward half-space and a distance above the half-space
boundary in reverse. The kernel checks these implications, including the
zero and half-space exclusions.

The kernel discharges 15 TCP/IP groups with the discriminator alone,
including ARP retry. Universal proofs for the TCP send and transmit groups
combine it with the model's buffer invariant and complementary guards.
The frame receive audit leaves 25 of 28,441 rule pairs, all within TCP.
It leaves zero within the link-layer rules, zero crossing that partition,
and zero involving the malformed IPv4 length rule. Four
separate kernel checks cover the full left-hand rule catalog. An equality
proves that concatenating those blocks recovers the original catalog and
that their counts compose.

The malformed IPv4 length rule also has a raw preservation proof. A
checked dependency analysis shows that its diagnostic assignment touches
no slot read by the invariants. The proof covers successful execution and
all post-state invariants for arbitrary admitted pre-states. Remaining
raw rule and frame overlap obligations stay open.
