import TCPIPTransmitBounds

namespace TCPIPTransmit
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts TCPIPTransmitFacts
open EffectConditions EffectFootprint GuardedSuffix TimedObligations TCPIPSendWire
set_option maxRecDepth 16384

set_option maxHeartbeats 1800000 in
theorem first_empty_cache (s : Snapshot) (f : Values)
    (enabled : TypedMachine.eval s f (linkGuard .empty) = true)
    (valid : invariantsHold model s = true) : Post s f true .empty e1597 := by
  obtain ⟨mac, noExpiry⟩ := pending_cache_requirements s f enabled valid
  change (((TypedMachine.eval s f e1587 && true) && TypedMachine.eval s f e1592) && true) = true
  simp [mac, noExpiry]

end TCPIPTransmit
