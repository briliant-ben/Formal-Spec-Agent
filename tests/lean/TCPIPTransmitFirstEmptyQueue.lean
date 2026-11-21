import TCPIPTransmitFirstEmptyAlign0
import TCPIPTransmitFirstEmptyAlign1
import TCPIPTransmitFirstEmptyAlign2
import TCPIPTransmitFirstEmptyAlign3

namespace TCPIPTransmit
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts TCPIPTransmitFacts
open EffectConditions EffectFootprint GuardedSuffix TimedObligations TCPIPSendWire
set_option maxRecDepth 16384

set_option maxHeartbeats 1800000 in
theorem first_empty_queue (s : Snapshot) (f : Values) :
    Each (Post s f true .empty) queueClauses := by
  have aligned : queueClauses.map (postChecks true .empty) =
      (queueChecks queuePacket (.equal .text e34 e34)).map (fun e => [e]) := by
    change [postChecks true .empty e1612, postChecks true .empty e1614,
      postChecks true .empty e1615, postChecks true .empty e1721] =
      [[(queueChecks queuePacket (.equal .text e34 e34))[0]'(by decide)],
       [(queueChecks queuePacket (.equal .text e34 e34))[1]'(by decide)],
       [(queueChecks queuePacket (.equal .text e34 e34))[2]'(by decide)],
       [(queueChecks queuePacket (.equal .text e34 e34))[3]'(by decide)]]
    rw [first_empty_align0, first_empty_align1, first_empty_align2, first_empty_align3]
  exact queue_from_post s f _ _ _ aligned queue_bound queue_minimum rfl

end TCPIPTransmit
