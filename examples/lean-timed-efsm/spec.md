# Timed Cell revision 1

This controller-frozen benchmark extends typed-cell semantics with a real timer.
It is a generic semantics benchmark, not a TCPIP protocol or an RFC claim.
Protocol IR remains the authority for the eventual executable model.

## Schema and initial context

States, in order: COLD, HOT. Initial state COLD, time0, no active timers.
Variables, in order: buf:bytes=[], n:int=0, cursor:seq32=0, label:string="",
accepted:bool=false. Values are mathematical integers, Unicode scalar strings,
full byte sequences and modulo2^32 sequence numbers. No bounded string/byte
projection restricts the universal formal obligations. Native implementation
capacities are a separate explicit domain.

Events, in order: application app.put with payload:bytes, sequence:seq32,
delta:int, label:string, allow:bool; timer timer.expiry with no fields.
Timer expiry raises timer.expiry. An external caller cannot inject timer events.
Messages cell.accept, cell.reject and cell.expired each contain the complete
resulting variables in buf,n,cursor,label,accepted order.

## Ordered rules

Rules in order: PUT.ACCEPT.COLD, PUT.REJECT.COLD, PUT.ACCEPT.HOT,
PUT.REJECT.HOT, EXPIRY.HOT. Acceptance in either state requires allow=true AND
length(payload)<=16. Rejection is the exact complement.

Acceptance assigns buf=payload, then n=length(updated buf), then
cursor=(sequence+delta) modulo2^32, label=event label, accepted=true; arms expiry
for10ms from the current logical time (replacing its prior deadline); emits
cell.accept with all five resulting values and targets HOT.

Rejection assigns only accepted=false and emits cell.reject with all five
resulting values. State, other variables and any existing expiry deadline stay
unchanged; rejected inputs do not refresh the timer.

On timer.expiry in HOT, the fired timer is removed before the ordered actions.
Assign buf=[], then n=0, label="", accepted=false; leave cursor unchanged; emit
cell.expired with all five resulting values and target COLD. There is no expiry
rule in COLD. Invariants hold initially and after every successful transition:
0<=n<=16; n=length(buf); expiry is active iff state HOT; COLD implies n=0 and
label="". There is no invariant equating accepted with timer activity.

## Scheduler and failure contracts

Before an external operation or tick at T, execute each active timer with
deadline<=T in earliest(deadline,name) order. Each timer transition is an actual
IR rule. Then execute the external event, if any, at T. Thus a put at the expiry
deadline first expires the old value, then applies the put. Tick with no due
transition changes only time. Backward time returns the original snapshot with
no partial trace or emissions. The entire timer-prefix/external operation is
atomic. No adapter generates expiry outputs, refreshes a timer or clears data.

## Frozen operations for independent oracle construction

Use one case with the initial context above and these operations in order:

1. dispatch at0: app.put payload[0,128,255,7], sequence4294967295, delta1,
   label="开\n\u0000", allow=true.
2. dispatch at5: app.put payload[0..16] inclusive, sequence123, delta0,
   label="ignored", allow=true.
3. dispatch at10: app.put payload[], sequence0, delta-1,
   label="", allow=true. The due expiry must precede this put.
4. tick at20.
5. dispatch at20: app.put payload[9], sequence7, delta0,
   label="disabled", allow=false.
6. dispatch at21: app.put payload[0,255,1,254,2,253,3,252,4,251,5,250,6,249,7,248],
   sequence1, delta-2, label="sixteen", allow=true.
7. dispatch at25: app.put payload[], sequence0, delta4294967296,
   label="wrap", allow=true. This refreshes deadline31 to35.
8. tick at31. There is no expiry here.
9. tick at35.
10. tick at34. This is a backward-time error with snapshot rollback.

All successful operations fix complete post-snapshots and full ordered trace
rows (rule, event with complete fields, time, after, all emissions). No-due ticks
have empty trace. The final error fixes fault time, original snapshot and empty
trace. The independent oracle must be authored before running the model.

## Exclusions

No reachability, native arithmetic/memory/compiler or English-specification
proof is claimed. The forthcoming model-specific timer coverage, static timer-ID
well-formedness, raw preservation and batch composition must be discharged;
generic bridge lemmas alone do not certify this timed model or the TCPIP case.
