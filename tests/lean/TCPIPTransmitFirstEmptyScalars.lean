import TCPIPTransmitBounds

namespace TCPIPTransmit
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts TCPIPTransmitFacts
open EffectConditions EffectFootprint GuardedSuffix TimedObligations TCPIPSendWire
set_option maxRecDepth 16384

set_option maxHeartbeats 1800000 in
theorem first_empty_e1594 (s : Snapshot) (f : Values) : Post s f true .empty e1594 := by rfl

set_option maxHeartbeats 1800000 in
theorem first_empty_e1601 (s : Snapshot) (f : Values) : Post s f true .empty e1601 := by rfl

set_option maxHeartbeats 1800000 in
theorem first_empty_e1604 (s : Snapshot) (f : Values) : Post s f true .empty e1604 := by rfl

set_option maxHeartbeats 1800000 in
theorem first_empty_e1628 (s : Snapshot) (f : Values) : Post s f true .empty e1628 := by rfl


end TCPIPTransmit
