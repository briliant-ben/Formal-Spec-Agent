import TCPIPTransmitBounds

namespace TCPIPTransmit
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts TCPIPTransmitFacts
open EffectConditions EffectFootprint GuardedSuffix TimedObligations TCPIPSendWire
set_option maxRecDepth 16384

set_option maxHeartbeats 1800000 in
theorem continued_pending_link (s : Snapshot) (f : Values)
    (enabled : TypedMachine.eval s f (linkGuard .pending) = true)
    (valid : invariantsHold model s = true) :
    Each (Post s f false .pending) (linkClauses .pending) := by
  have aligned : queueClauses.map (postChecks false .pending) =
      (queueChecks queuePacket e35).map (fun e => [e]) := by
    rfl
  exact queue_from_post s f _ _ _ aligned queue_bound queue_minimum enabled

end TCPIPTransmit
