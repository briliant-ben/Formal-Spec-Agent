import TCPIPTransmitBounds

namespace TCPIPTransmit
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts TCPIPTransmitFacts
open EffectConditions EffectFootprint GuardedSuffix TimedObligations TCPIPSendWire
set_option maxRecDepth 16384

set_option maxHeartbeats 1800000 in
theorem first_resolved_link (s : Snapshot) (f : Values)
    (enabled : TypedMachine.eval s f (linkGuard .resolved) = true)
    (valid : invariantsHold model s = true) :
    Each (Post s f true .resolved) (linkClauses .resolved) := by
  trivial


end TCPIPTransmit
