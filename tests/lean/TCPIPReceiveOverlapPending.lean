import TCPIPReceiveLinkFacts

namespace TCPIPReceiveData
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts
open EffectConditions EffectFootprint GuardedSuffix TimedObligations
set_option maxRecDepth 16384

theorem overlap_pending_clauses (s : Snapshot) (f : Values)
    (valid : invariantsHold model s = true) (enabled : TypedMachine.eval s f (linkGuard .pending) = true)
    (est : TypedMachine.eval s f e923 = true) (room : 1 ≤ TypedMachine.eval s f e1233) :
    Each (fun inv => checkedClause (rule true .pending) inv s f) (affected .pending) := by
  have buffer := within_buffer s f true .pending room
  have established := established_buffer s f true .pending est
  have window := advertised_window s f true .pending
  have packet := packet_bound s f true .pending
  have queue := pending_queue s f true enabled
  exact ⟨rfl, queue, rfl, buffer, established, window, packet, rfl, trivial⟩

end TCPIPReceiveData
