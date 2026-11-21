import TCPIPReceiveLinkFacts

namespace TCPIPReceiveData
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts
open EffectConditions EffectFootprint GuardedSuffix TimedObligations
set_option maxRecDepth 16384

set_option maxHeartbeats 2200000 in
theorem inorder_empty_clauses (s : Snapshot) (f : Values)
    (valid : invariantsHold model s = true) (enabled : TypedMachine.eval s f (linkGuard .empty) = true)
    (est : TypedMachine.eval s f e923 = true) (room : 1 ≤ TypedMachine.eval s f e1233) :
    Each (fun inv => checkedClause (rule false .empty) inv s f) (affected .empty) := by
  have buffer := within_buffer s f false .empty room
  have established := established_buffer s f false .empty est
  have window := advertised_window s f false .empty
  have packet := packet_bound s f false .empty
  have cache := empty_cache s f false enabled valid
  exact ⟨rfl, cache, rfl, rfl, rfl, rfl, rfl, rfl, buffer, established, window, packet, rfl, trivial⟩

end TCPIPReceiveData
