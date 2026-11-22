# Raw firing and scheduled preservation

This layer connects actual timer removal and selection to the typed raw
candidate semantics. The endpoint proof below instantiates its universal
contracts for the pinned concrete IR, with the documented admission conditions.

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

This early microstep evidence covers the stated unit. The later endpoint
proof and historical UNKNOWN receipts have separate input and scope bindings.


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
generated initial snapshot with arbitrary typed event fields. The full
ten-stage universal timed flow (`examples/lean-timed-efsm/flow.json`) and finite
batch replay certificate (`examples/lean-timed-efsm/task.json`) both pass on
Lean 4.35.0.

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
nonnegative request time and arbitrary typed fields. The completed TCP/IP timer contracts also establish this result for
arbitrary admitted snapshots with timers. The other thirteen declared external
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
For the 239 frame receive rules, sixteen kernel checks enumerate the exact
residual rule IDs across all 28,441 pairs. The 25 residuals are all TCP.
Six FIN acknowledgment exclusions follow from the invariant relating
`SND.NXT` and `SND.UNA` to the outstanding control sequence number.
Four old acknowledgment exclusions use the modular distance and the
16-byte buffer bound. Six duplicate-versus-future exclusions use zero
distance and nonnegative retransmission length. The other nine follow
from complementary predicates.

The frame catalog proves that concatenating the sixteen blocks recovers the
original rule list. Unique rule IDs bind each residual to the original
guard expressions. The kernel combines the checked frame group with the
other 17 groups to prove guard disjointness whenever the model invariants
hold. This statement applies to rules with the same source state and
event, over arbitrary field values. It does not prove that the invariants
hold after each rule or that every event is covered.

The raw preservation checker also accepts an unconditional guard equality
that forces a literal text assignment to write its slot's existing value.
For a sequence of actions, the proof carries equality of invariant inputs
forward from the guard's snapshot. Unrelated assignments and message
emissions may occur between these writes. A disjunction or a field
equality supplies no store fact, and an arm or cancel is outside this
checker.

The kernel checks 83 guarded-write obligations and 24 buffer-reset
obligations against the original model. For a leading empty-buffer
assignment, the proof keeps unaffected invariants and tracks the empty
buffer through the remaining actions. It then proves the original
post-state length bound and conditional empty-buffer invariant. It checks
that the original guard is unaffected by the assignment and requires the
remaining actions to preserve the temporary invariant. A timer firing is
outside both checks.

The kernel also proves preservation for the ARP query retry firing. The
pending invariant establishes that the query timer is active beforehand.
After removing the firing and rearming the same timer at its new
deadline, the set of active timer IDs is unchanged. The proof then checks
the updated retry count and the unchanged link state, including the
exact transition and its emitted message.

For firings that change timer activity, the effect checker substitutes each
original action into the required postconditions in reverse order. It
accounts for removing the firing before the first action, requires each
timer arm's delay to be positive at its actual position, and evaluates
invariants at the rule's target with zero event fields. Its soundness
theorem recovers the exact original candidate execution, including its
emitted messages. Unchanged invariant clauses can reuse the input
invariant evidence. The checker can certify clauses separately because
they refer to the same deterministic transition.

The ARP proofs use this checker for query start, cache expiration, and
query expiration with an empty queue, queued UDP, or queued TCP. Three
cache configuration proofs cover empty, pending, and resolved phases.
For the resolved phase, the proof carries the configured TTL through the
preceding assignment and checks the exact delay used by the timer arm.
The effect footprint checker tracks reads of store slots and timer IDs
in separate namespaces. It checks timer removal as well as all subsequent
actions. For rules that keep the machine state, clauses whose reads stay
unchanged follow directly from the input invariants. The checker still
requires evidence that the full firing succeeds.

The UDP delivery rules use this checker for all three ARP phases. Their
proofs derive the 1,472-byte payload bound from the original IPv4 packet
bound and UDP length equality, including the buffer slice's clipping
semantics.

The TCP application send-queue proof checks that its final literal
control-state write repeats the value established by the guard. Erasing
that write in the proof preserves the exact candidate, including its
message, because preceding actions leave that slot intact. For the
remaining effects, the input send-capacity guard bounds the sum of the
new send buffer and the retransmit buffer. Only two invariant clauses
need direct proofs.

Four TCP response cases send an empty TCP payload after a future ACK,
duplicate data, data ahead of the receive sequence, or data while the
window is zero. Each case has empty, pending, and resolved ARP variants.
Lean checks the ordered actions and machine states before reusing each
phase's proof. The resolved phase checks the emitted response's packet
length. The pending and empty phases also certify the queued packet and
its owner. The empty phase checks the new positive-delay timer arm and
the transition to pending. All twelve cases retain their original
guards and messages.

The TCP application-read proofs cover all three ARP phases. They prove
that dropping and clipping a byte slice cannot grow the receive buffer,
that the advertised window uses its updated length, and that the ACK
response satisfies the packet and queue invariants for each phase.

The effect checker computes the same action preconditions with a
forward environment for store and timer substitutions. Lean proves
equality with the backward construction for every rule, firing and
invariant list, including the exact order of positive-delay checks.
Unchanged reads reuse the environment directly, which avoids traversing
all output formulas after every action.

The acknowledgment proofs cover full and partial acknowledgments with
both accepted and stale window updates, and duplicate acknowledgments
with an accepted update. Trimming the acknowledged prefix preserves
the relation between the next send sequence and the remaining bytes,
including wraparound. The proofs also check the retransmit timer,
combined buffer capacity and the relation between remaining bytes and
the applicable receive window. Lean checks that each rule's original
guard and generated conditions match the shared proof.

The data receive proofs cover in-order and overlapping segments across
all three ARP phases. The original guards supply the available window.
The original slice clips the accepted suffix to that window, so
appending it keeps the receive buffer within 16 bytes. The window
advertisement uses the updated buffer length. The proofs also check the
packet bound and the queue, cache, and timer invariants for each phase.

The TCP retransmit proofs cover data and the control segments used in
SYN-SENT, SYN-RECEIVED, FIN-WAIT-1, CLOSING and LAST-ACK. Each of these
six cases has empty, pending and resolved ARP variants. Lean checks
that consuming and rearming the retransmit timer keeps it active, that
doubling the timeout and incrementing the retry count preserve their
bounds, and that queued or transmitted packets satisfy the length and
ownership constraints. The proof checks the actual control-state guard
and that the final action writes that same state.
The effect compiler proves that the ordered positive-delay checks are
independent of the selected postconditions. The octet bound checker
derives length bounds from actual packet expressions using concatenation,
slicing and fixed-width packing. These proofs quantify over all byte
values, including inputs to checksum expressions.

The six TCP data transmit firings cover first and continuing sends in
all three ARP phases. The original send count is capped by the queued
bytes, available window and four-byte segment limit. The proof splits
the send buffer at that count, checks the new retransmit-buffer length
against the window, and relates the updated send sequence to the new
buffer length across wraparound. The first send arms the timer with a
positive delay. A continuing send retains the already active timer.
Send and retransmit share the queue proof, with Lean checking each
original rule's generated queue obligations.

The eight close and abort firings that enter CLOSED without emitting a
reset share the same ordered timer and queue effects. The proof checks
that cancelling the three TCP timers meets the CLOSED-state conditions.
The prior phase implies that the TCP data buffers are already empty.
The queue proof checks both outcomes of the original ownership guard:
the TCP-owned packet is cleared along with its owner, while a queue
with any other owner retains its contents and metadata.

Twelve duplicate-FIN firings preserve the TCP control state in
CLOSE-WAIT, CLOSING, LAST-ACK and TIME-WAIT across the three ARP
phases. The proof uses the same packet and queue checks as retransmit.
The TIME-WAIT variants also restart the timer with a positive delay
and establish the timer-activity invariant for that control state.

The same proof also covers twelve replies to invalid acknowledgments,
invalid SYN-ACKs, and SYNs received in CLOSED. Lean checks that each
reply retains its original TCP phase. When a CLOSED endpoint can send
its reset directly, the proof also checks the ordered release of any
TCP-owned queued packet and the preservation of other queue owners.

Eighteen more control replies cover ACK, SYN-ACK and FIN received in
CLOSED or LISTEN. These rules preserve the original phase, and the
same queue proof checks whether a reset is transmitted or queued.

Seven user-timeout and TIME-WAIT-expiry firings, and seventeen
received-reset firings, extend the CLOSED cleanup proof. Lean checks
timer-event membership for the timer firings and the original input
guards for the received resets. In the ESTABLISHED cases, the proof
checks all three buffer clears, the reset of the local receive window
and the existing nonnegative peer-window bound.

Twenty more firings cover aborts that send a reset across the three
ARP phases, passive open and passive reset into LISTEN, and reset
inputs ignored in CLOSED. The abort proofs check both immediate
transmission with queue release and the path that queues the reset
until ARP resolves. The passive paths use the actual prior-phase
guard to establish that the data buffers are empty.

Nine ARP learning firings establish the six-byte cache address from
the actual frame-length guard. The same proof checks cache timer
activation, query cancellation or retention, and queue clearing when
learning resolves a pending packet. Three ICMP reply firings use the
validated input length to bound the rebuilt IPv4 and ICMP data before
Ethernet padding. Five malformed TCP frame drops keep the CLOSED
state and check the same conditional queue release as ignored resets.

Three UDP transmission firings establish that the original action
sequence produces a 28-byte IP/UDP header plus the full payload.
The proof checks the bound of 1,500 bytes and the pending queue's
UDP ownership, including an empty payload.

The five timer IDs and all 30 timer firings have an exact Lean catalog.
For any active timer in an admitted snapshot, the model invariants
provide an enabled rule. The proof checks ARP retry and queue ownership,
TCP control phases and the retransmit buffer. The model's declared
targets and timer arms, unique IDs, guard disjointness, coverage and
preservation then instantiate the actual scheduler's batch theorem.
It reaches any nondecreasing requested time with all remaining timers
strictly in the future and invariants preserved along the trace.
The eight unwired external events return uncovered with rollback even
when the timer prefix fires. External rule preservation remains separate.

Nine active, passive and simultaneous TCP open firings preserve
the control-sequence relation and timer requirements in SYN-SENT or
SYN-RECEIVED. The proof checks the positive delays of newly armed
timers, retention of the existing timers for simultaneous open, and
the original packet and queue effects across the three ARP phases.
Lean also checks that the model's actual initial snapshot satisfies
the admission conditions for the timer scheduler.

Twenty-one TCP handshake acknowledgments establish the ESTABLISHED
invariants for initial, retry and multiple-retry cases. The proof
connects the actual wire acknowledgment to the next send sequence,
checks the decoded receive window's range, and preserves the flight,
timer and retransmit-buffer constraints. It covers both ACK-only
reception and packet-emitting responses in the three ARP phases.

Twenty-one TCP closing firings check local FIN, acknowledgments of
FIN and peer FIN across the admitted states and ARP phases. The proofs
use the prior buffer, sequence and timer invariants, and check when
the transitions preserve a timer, arm it or cancel it. The wire paths
check the emitted packet bound and pending queue ownership.

For the pinned TCP/IP IR the checked preservation catalog equals the
authoritative list of all 335 firings after sorting. Lean compares the
full rule values and timer IDs. The endpoint theorem covers every
declared external event at a nondecreasing time from an admitted
pre-state. The scheduler first drains the due timers. When no external
guard matches, dispatch returns uncovered and rolls back. When a
guard matches, dispatch succeeds and preserves the invariants across
the returned trace. Guard disjointness prevents a conflicting match.

The compiled Lean batch interpreter also matches the 19 operations
in the archived generated C session with Linux peers. Its runtime
renderer places each operation in its own Lean declaration to keep
MTU-sized input elaboration within the existing budget. The first
resource failure and the successful replay use the same model and
literal observations. See the [replay evidence](../evidence/lean-tcpip-replay-20261121/README.md).

The public Lean-only timed flow connects the proof audit to generated
C observations. The case-study and legacy-backend migration status is
tracked separately.

## Running the timed proof check

`formal-spec-agent lean-timed-check` compiles reviewed Lean modules
against an `Approved.lean` generated from the pinned Protocol IR.
The proof manifest uses `fsa-lean-timed-proof-manifest-v1`, with
`model` mapping root and base filenames relative to the root IR directory
to SHA-256 digests and `modules` listing ordered `module` and `sha256`
entries. The Lean files sit next to the manifest. The last module,
`TimedProof`, exports these theorems:

| Theorem | Contract |
|---|---|
| `TimedProof.initial` | The IR's default state is admitted at time zero |
| `TimedProof.timers` | The scheduler's timer, domain and guard contracts |
| `TimedProof.preservation` | Every raw firing in the authoritative IR catalog preserves the declared invariants |

The checker instantiates timer advance and external dispatch theorems,
checks their axiom dependencies, and records frozen inputs, compiler
logs and verdicts. The digest supplied by the caller binds the reviewed
manifest. These proof modules are executable Lean source.

```sh
formal-spec-agent lean-timed-check model.json \
  --proof-manifest proofs/manifest.json --proof-sha256 "$REVIEWED_PROOF_SHA256" \
  --out /tmp/timed-proof-check
```

Both the [mailbox timed flow](../examples/mailbox/task.json) and the
[Timed Cell flow](../examples/lean-timed-efsm/flow.json) connect the same check
to the C generation and comparison stages. Its `formal` object contains `strategy: "lean-timed"`,
`manifest` and `manifest_sha256`. Declare the manifest and each
proof module under `sources` and pass the reviewed flow digest through
`--task-sha256`. Flow verification revalidates the retained model,
proof sources and compiler receipts. Run the pinned flow again for a
fresh kernel check. Test generation reports reachable observations
within its declared exploration independently of the proof verdict.

## Reviewed compilation groups

Manifest `fsa-lean-timed-proof-manifest-v2` adds `compile_groups` to the
v1 fields. Each group contains one or two caller module names; flattening the
groups must reproduce the complete ordered `modules` list exactly. `TimedProof`
is a final singleton. The caller-reviewed manifest digest binds the schedule.
V1 remains sequential.

The fixed library and generated `Approved` module compile sequentially, followed
by the reviewed groups and a final singleton `TimedAudit`. At most two compiler
processes run concurrently. Every module still compiles from fresh source with
the same per-module deadline; no compiled-object cache or proof omission is used.
V2 requires simple single-line import headers and rejects known imports from
the same or a later group. Unsupported import headers are explicitly refused.
Executable Lean sources and their suitability for concurrent execution remain
caller-reviewed trust assumptions; this is not a sandbox for hostile Lean code.

The v2 result binds the complete schedule and records every started sibling in
canonical source order. If a compiler exits unsuccessfully or times out, its
sibling result is retained and no later group starts. Read-only inspection
requires a complete prefix of groups and rejects failures hidden by a successful
sibling, altered schedules, missing or reordered receipts, and Boolean/numeric
exit-code aliases. A pass still requires every source and the axiom audit.
An interrupted worker without a final report is not a checked proof.
