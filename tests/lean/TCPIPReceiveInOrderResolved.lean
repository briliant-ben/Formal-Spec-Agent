import TCPIPReceiveLinkFacts

namespace TCPIPReceiveData
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts
open EffectConditions EffectFootprint GuardedSuffix TimedObligations
set_option maxRecDepth 16384

theorem inorder_resolved_clauses (s : Snapshot) (f : Values)
    (valid : invariantsHold model s = true) (enabled : TypedMachine.eval s f (linkGuard .resolved) = true)
    (est : TypedMachine.eval s f e923 = true) (room : 1 ≤ TypedMachine.eval s f e1233) :
    Each (fun inv => checkedClause (rule false .resolved) inv s f) (affected .resolved) := by
  have buffer := within_buffer s f false .resolved room
  have established := established_buffer s f false .resolved est
  have window := advertised_window s f false .resolved
  have packet := packet_bound s f false .resolved
  exact ⟨buffer, established, window, packet, trivial⟩

end TCPIPReceiveData
