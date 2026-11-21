import TCPIPReceiveLinkFacts

namespace TCPIPReceiveData
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts
open EffectConditions EffectFootprint GuardedSuffix TimedObligations
set_option maxRecDepth 16384

set_option maxHeartbeats 2200000 in
theorem inorder_pending_clauses (s : Snapshot) (f : Values)
    (valid : invariantsHold model s = true) (enabled : TypedMachine.eval s f (linkGuard .pending) = true)
    (est : TypedMachine.eval s f e923 = true) (room : 1 ≤ TypedMachine.eval s f e1233) :
    Each (fun inv => checkedClause (rule false .pending) inv s f) (affected .pending) := by
  have buffer := within_buffer s f false .pending room
  have established := established_buffer s f false .pending est
  have window := advertised_window s f false .pending
  have packet := packet_bound s f false .pending
  have queue := pending_queue s f false enabled
  exact ⟨rfl, queue, rfl, buffer, established, window, packet, rfl, trivial⟩

end TCPIPReceiveData
