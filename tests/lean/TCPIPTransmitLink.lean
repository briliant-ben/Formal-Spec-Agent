import TCPIPTransmitFirstEmpty
import TCPIPTransmitFirstPending
import TCPIPTransmitFirstResolved
import TCPIPTransmitContinuedEmpty
import TCPIPTransmitContinuedPending
import TCPIPTransmitContinuedResolved

namespace TCPIPTransmit
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts TCPIPTransmitFacts
open EffectConditions EffectFootprint GuardedSuffix TimedObligations TCPIPSendWire
set_option maxRecDepth 16384

set_option maxHeartbeats 1800000 in
theorem link_checks (s : Snapshot) (f : Values) (first : Bool) (phase : LinkPhase)
    (enabled : TypedMachine.eval s f (linkGuard phase) = true)
    (valid : invariantsHold model s = true) :
    Each (Post s f first phase) (linkClauses phase) := by
  cases first <;> cases phase
  · exact continued_empty_link s f enabled valid
  · exact continued_pending_link s f enabled valid
  · exact continued_resolved_link s f enabled valid
  · exact first_empty_link s f enabled valid
  · exact first_pending_link s f enabled valid
  · exact first_resolved_link s f enabled valid

theorem positive_delays (s : Snapshot) (f : Values) (first : Bool) (phase : LinkPhase)
    (valid : invariantsHold model s = true) : holds (delays first phase) s f = true := by
  have timeout : 1000 ≤ TypedMachine.eval s f e566 :=
    of_decide_eq_true (List.all_eq_true.mp valid e1680 (by rw [model_invariants]; simp))
  have positive := Int.le_trans (by decide : (1 : Int) ≤ 1000) timeout
  cases first <;> cases phase
  all_goals first | rfl | (change (decide (1 ≤ TypedMachine.eval s f e566) && true) = true; simp [positive])


end TCPIPTransmit
