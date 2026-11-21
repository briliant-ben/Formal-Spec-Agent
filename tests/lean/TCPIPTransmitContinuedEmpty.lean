import TCPIPTransmitBounds

namespace TCPIPTransmit
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts TCPIPTransmitFacts
open EffectConditions EffectFootprint GuardedSuffix TimedObligations TCPIPSendWire
set_option maxRecDepth 16384

set_option maxHeartbeats 1800000 in
theorem continued_empty_link (s : Snapshot) (f : Values)
    (enabled : TypedMachine.eval s f (linkGuard .empty) = true)
    (valid : invariantsHold model s = true) :
    Each (Post s f false .empty) (linkClauses .empty) := by
  have aligned : queueClauses.map (postChecks false .empty) =
      (queueChecks queuePacket (.equal .text e34 e34)).map (fun e => [e]) := by
    rfl
  have queued := queue_from_post s f _ _ _ aligned queue_bound queue_minimum rfl
  obtain ⟨mac, noExpiry⟩ := pending_cache_requirements s f enabled valid
  have cache : Post s f false .empty e1597 := by
    change (((TypedMachine.eval s f e1587 && true) && TypedMachine.eval s f e1592) && true) = true
    all_goals simp [mac, noExpiry]
  exact ⟨rfl, cache, rfl, rfl, queued.1, queued.2.1, queued.2.2.1, rfl,
    queued.2.2.2.1, trivial⟩

end TCPIPTransmit
