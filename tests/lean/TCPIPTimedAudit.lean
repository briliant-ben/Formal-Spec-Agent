import Approved
import BatchTotality

namespace TCPIPAudit
open FormalSpecAgent FormalSpecAgent.TypedMachine FormalSpecAgent.TypedIR
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

private theorem exclusive {a b : Bool} {v x y : String} (distinct : x ≠ y)
    (aKey : a = true → v = x) (bKey : b = true → v = y) : a = false ∨ b = false := by
  cases a <;> cases b <;> simp_all

private theorem emptyKey (s : Snapshot) (f : Values) (h : TypedMachine.eval s f rule_5.guard = true) :
    s.values.texts 25 = "EMPTY" := by
  change (decide (s.values.texts 25 = "EMPTY") && TypedMachine.eval s f e50) = true at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

private theorem pendingKey (s : Snapshot) (f : Values) (h : TypedMachine.eval s f rule_10.guard = true) :
    s.values.texts 25 = "PENDING" := by
  change (decide (s.values.texts 25 = "PENDING") && TypedMachine.eval s f e50) = true at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

private theorem resolvedKey (s : Snapshot) (f : Values) (h : TypedMachine.eval s f rule_13.guard = true) :
    s.values.texts 25 = "RESOLVED" := by
  change (decide (s.values.texts 25 = "RESOLVED") && TypedMachine.eval s f e50) = true at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem cacheConfigDisjoint : Approved.conflict_3 := by
  intro s f _ left leftIn right rightIn distinct _
  simp [conflictGroup_3] at leftIn rightIn
  rcases leftIn with rfl | rfl | rfl <;> rcases rightIn with rfl | rfl | rfl
  all_goals try exact (distinct rfl).elim
  · exact exclusive (by decide) (emptyKey s f) (pendingKey s f)
  · exact exclusive (by decide) (emptyKey s f) (resolvedKey s f)
  · exact exclusive (by decide) (pendingKey s f) (emptyKey s f)
  · exact exclusive (by decide) (pendingKey s f) (resolvedKey s f)
  · exact exclusive (by decide) (resolvedKey s f) (emptyKey s f)
  · exact exclusive (by decide) (resolvedKey s f) (pendingKey s f)

#print axioms cacheConfigDisjoint

set_option maxRecDepth 16384 in
theorem endpoint_raw_exact : Approved.raw_catalog_exact := by rfl
set_option maxRecDepth 16384 in
theorem endpoint_conflicts_exact : Approved.conflict_catalog_exact := by rfl
#print axioms endpoint_raw_exact
#print axioms endpoint_conflicts_exact

end TCPIPAudit
