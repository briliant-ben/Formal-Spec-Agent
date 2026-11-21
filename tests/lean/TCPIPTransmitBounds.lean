import TCPIPTransmitLayout

namespace TCPIPTransmit
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts TCPIPTransmitFacts
open EffectConditions EffectFootprint GuardedSuffix TimedObligations TCPIPSendWire
set_option maxRecDepth 16384

set_option maxHeartbeats 1800000 in
theorem packet_bound (s : Snapshot) (f : Values) (first : Bool) (phase : LinkPhase) :
    Post s f first phase e1706 := by
  apply OctetBounds.all_sound (postChecks first phase e1706) (context s f)
  cases first <;> cases phase <;> decide +kernel

def queuePacket : Expr .octets :=
  match postChecks true .pending e1612 with
  | [.intLe (.bytesLength packet) _] => packet
  | _ => .literal .octets []

theorem queue_bound :
    OctetBounds.certifies (.intLe (.bytesLength queuePacket) e244) = true := by decide +kernel

theorem queue_minimum : 28 ≤ OctetBounds.lower queuePacket := by decide +kernel


end TCPIPTransmit
