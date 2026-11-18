import Approved
import BatchTotality

namespace TCPIPAudit
open FormalSpecAgent.TypedMachine
open FormalSpecAgent.BatchMachine FormalSpecAgent.BatchTotality
open Approved

def absent : List Nat := TCPIP_ABSENT_IDS

/-- Check the complete partition using the actual rule events and declared
    external IDs, independent of field values and guard outcomes. -/
theorem absent_external_exact :
    model.externalEvents.filter (fun event => !(model.rules.map Rule.event).contains event)
      = absent := by decide

theorem absent_packet_rolls_back (states ids : List Nat) (limit : Int)
    (contract : TimerContracts model states ids) (s : Snapshot)
    (admitted : Admitted model states ids s) (bound : s.now ≤ limit)
    (event : Nat) (fields : FormalSpecAgent.TypedIR.Values) (member : event ∈ absent) :
    dispatch model s event fields limit = .error .uncovered ∧
      rollback s (dispatch model s event fields limit) = s := by
  rw [← absent_external_exact] at member
  obtain ⟨declared, notWired⟩ := List.mem_filter.mp member
  have witness : AbsentExternal model event := ⟨declared, by simpa using notWired⟩
  exact dispatch_absent model states ids limit contract s admitted bound event fields witness

theorem absent_initial_dispatch (limit : Int) (bound : 0 ≤ limit)
    (event : Nat) (fields : FormalSpecAgent.TypedIR.Values) (member : event ∈ absent) :
    dispatch model initial event fields limit = .error .uncovered ∧
      rollback initial (dispatch model initial event fields limit) = initial := by
  rw [← absent_external_exact] at member
  obtain ⟨declared, notWired⟩ := List.mem_filter.mp member
  have witness : AbsentExternal model event := ⟨declared, by simpa using notWired⟩
  exact dispatch_absent_without_timers model initial limit rfl bound event fields witness

#print axioms absent_initial_dispatch
#print axioms absent_external_exact
#print axioms absent_packet_rolls_back
end TCPIPAudit
