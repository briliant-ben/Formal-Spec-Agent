import TCPIPTransmitBounds

namespace TCPIPTransmit
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts TCPIPTransmitFacts
open EffectConditions EffectFootprint GuardedSuffix TimedObligations TCPIPSendWire
set_option maxRecDepth 16384

set_option maxHeartbeats 1800000 in
theorem first_empty_align2 : postChecks true .empty e1615 =
    [(queueChecks queuePacket (.equal .text e34 e34))[2]'(by decide)] := by rfl

end TCPIPTransmit
