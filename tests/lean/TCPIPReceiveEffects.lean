import TCPIPReceiveInOrderEmpty
import TCPIPReceiveInOrderPending
import TCPIPReceiveInOrderResolved
import TCPIPReceiveOverlapEmpty
import TCPIPReceiveOverlapPending
import TCPIPReceiveOverlapResolved

namespace TCPIPReceiveData
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts
open EffectConditions EffectFootprint GuardedSuffix TimedObligations
set_option maxRecDepth 16384

theorem link_clauses (s : Snapshot) (f : Values) (overlap : Bool) (phase : LinkPhase)
    (valid : invariantsHold model s = true) (enabled : TypedMachine.eval s f (linkGuard phase) = true)
    (est : TypedMachine.eval s f e923 = true) (room : 1 ≤ TypedMachine.eval s f e1233) :
    Each (fun inv => checkedClause (rule overlap phase) inv s f) (affected phase) := by
  cases overlap <;> cases phase
  · exact inorder_empty_clauses s f valid enabled est room
  · exact inorder_pending_clauses s f valid enabled est room
  · exact inorder_resolved_clauses s f valid enabled est room
  · exact overlap_empty_clauses s f valid enabled est room
  · exact overlap_pending_clauses s f valid enabled est room
  · exact overlap_resolved_clauses s f valid enabled est room

end TCPIPReceiveData
