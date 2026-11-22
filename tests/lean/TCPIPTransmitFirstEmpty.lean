import TCPIPTransmitFirstEmptyQueue
import TCPIPTransmitFirstEmptyCache
import TCPIPTransmitFirstEmptyScalars

namespace TCPIPTransmit
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts TCPIPTransmitFacts
open EffectConditions EffectFootprint GuardedSuffix TimedObligations TCPIPSendWire
set_option maxRecDepth 16384

set_option maxHeartbeats 1800000 in
theorem first_empty_link (s : Snapshot) (f : Values)
    (enabled : TypedMachine.eval s f (linkGuard .empty) = true)
    (valid : invariantsHold model s = true) :
    Each (Post s f true .empty) (linkClauses .empty) := by
  have queued := first_empty_queue s f
  exact ⟨first_empty_e1594 s f, first_empty_cache s f enabled valid,
    first_empty_e1601 s f, first_empty_e1604 s f, queued.1, queued.2.1,
    queued.2.2.1, first_empty_e1628 s f, queued.2.2.2.1, trivial⟩

end TCPIPTransmit
