import TCPIPReceiveLinkFacts

namespace TCPIPReceiveData
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts
open EffectConditions EffectFootprint GuardedSuffix TimedObligations
set_option maxRecDepth 16384

theorem overlap_empty_clauses (s : Snapshot) (f : Values)
    (valid : invariantsHold model s = true) (enabled : TypedMachine.eval s f (linkGuard .empty) = true)
    (est : TypedMachine.eval s f e923 = true) (room : 1 ≤ TypedMachine.eval s f e1233) :
    Each (fun inv => checkedClause (rule true .empty) inv s f) (affected .empty) := by
  have buffer := within_buffer s f true .empty room
  have established := established_buffer s f true .empty est
  have window := advertised_window s f true .empty
  have packet := packet_bound s f true .empty
  have cache := empty_cache s f true enabled valid
  exact ⟨rfl, cache, rfl, rfl, rfl, rfl, rfl, rfl, buffer, established, window, packet, rfl, trivial⟩

end TCPIPReceiveData
