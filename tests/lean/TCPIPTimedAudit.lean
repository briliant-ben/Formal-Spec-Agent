import Approved
import GuardDiscriminators
import ResetPreservation
import TCPIPTimerRules
import TCPIPQueries
import TCPIPCacheConfig
import TCPIPUDPDeliver
import TCPIPSendQueue
import TCPIPEmptyResponses
import TCPIPApplicationReadEmpty
import FrameCatalogExact

namespace TCPIPAudit
open FormalSpecAgent FormalSpecAgent.TypedMachine FormalSpecAgent.TypedIR
open FormalSpecAgent.BatchMachine FormalSpecAgent.BatchTotality
open Approved GuardDiscriminators TimedObligations

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

/-- The group IDs refer to the exact independently checked conflict catalog. -/
theorem closed_groups :
    Each (ConflictFree model) [conflictGroup_0, conflictGroup_1, conflictGroup_2, conflictGroup_3,
      conflictGroup_5, conflictGroup_6, conflictGroup_7, conflictGroup_8,
      conflictGroup_9, conflictGroup_10, conflictGroup_11, conflictGroup_12,
      conflictGroup_13, conflictGroup_14, conflictGroup_17] :=
  ⟨conflict_from_empty model _ rfl, conflict_from_empty model _ rfl,
    conflict_from_empty model _ rfl, conflict_from_empty model _ rfl,
    conflict_from_empty model _ rfl, conflict_from_empty model _ rfl,
    conflict_from_empty model _ rfl, conflict_from_empty model _ rfl,
    conflict_from_empty model _ rfl, conflict_from_empty model _ rfl,
    conflict_from_empty model _ rfl, conflict_from_empty model _ rfl,
    conflict_from_empty model _ rfl, conflict_from_empty model _ rfl,
    conflict_from_empty model _ rfl, trivial⟩

set_option maxRecDepth 16384 in
theorem malformed_length_preserves : raw_334_external :=
  FormalSpecAgent.InvariantFootprint.external_rule_keeps_invariants model rule_334 rfl
    (by decide +kernel)

def endpoint_guarded_checks : List (Rule × Option Nat) :=
  FormalSpecAgent.InvariantFootprint.guardedRawChecks model declaredTimers

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem endpoint_guarded_count : endpoint_guarded_checks.length = 83 := by decide +kernel

theorem endpoint_guarded_preservation :
    Each (fun pairing => TypedFiringContracts.FiringPreserves model pairing.1 pairing.2)
      endpoint_guarded_checks :=
  FormalSpecAgent.InvariantFootprint.guardedRawChecks_sound model declaredTimers

#print axioms malformed_length_preserves
#print axioms endpoint_guarded_count
#print axioms endpoint_guarded_preservation

private theorem each_append {items rest : List α} {property : α → Prop}
    (left : Each property items) (right : Each property rest) :
    Each property (items ++ rest) := by
  induction items with
  | nil => exact right
  | cons _ _ ih => exact ⟨left.1, ih left.2⟩

def endpoint_reset_checks : List (Rule × Option Nat) :=
  ResetPreservation.resetChecks model declaredTimers

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem endpoint_reset_count : endpoint_reset_checks.length = 24 := by decide +kernel

def endpoint_preservation_checks :=
  endpoint_guarded_checks ++ endpoint_reset_checks ++ [(rule_3, some 1)] ++
    TCPIPQueries.firings ++ TCPIPCacheConfig.firings ++ TCPIPUDPDeliver.firings ++ [(rule_238, none)] ++
    TCPIPEmptyResponses.firings ++ TCPIPApplicationReadEmpty.firings

theorem endpoint_preservation_count : endpoint_preservation_checks.length = 135 := by
  simp only [endpoint_preservation_checks, List.length_append, endpoint_guarded_count,
    endpoint_reset_count] <;> rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem endpoint_preservation_unique :
    (endpoint_preservation_checks.map (fun p => (p.1.id, p.2))).Nodup := by decide +kernel

theorem endpoint_preservation_checked :
    Each (fun p => TypedFiringContracts.FiringPreserves model p.1 p.2) endpoint_preservation_checks :=
  each_append (each_append (each_append (each_append (each_append (each_append (each_append
    (each_append endpoint_guarded_preservation (ResetPreservation.resetChecks_sound model declaredTimers))
    ⟨TCPIPTimerRules.query_retry, trivial⟩) TCPIPQueries.checked) TCPIPCacheConfig.checked)
    TCPIPUDPDeliver.checked) ⟨TCPIPSendQueue.send_queue, trivial⟩) TCPIPEmptyResponses.checked)
    TCPIPApplicationReadEmpty.checked

theorem endpoint_tcp_read_members :
    Each (fun p => p ∈ rawChecks model declaredTimers) TCPIPApplicationReadEmpty.firings :=
  TCPIPApplicationReadEmpty.members

#print axioms endpoint_tcp_read_members

theorem endpoint_tcp_response_members :
    Each (fun p => p ∈ rawChecks model declaredTimers) TCPIPEmptyResponses.firings :=
  TCPIPEmptyResponses.members

#print axioms endpoint_tcp_response_members

theorem endpoint_arp_members :
    Each (fun p => p ∈ rawChecks model declaredTimers) (TCPIPQueries.firings ++ TCPIPCacheConfig.firings) :=
  each_append TCPIPQueries.members TCPIPCacheConfig.members

theorem endpoint_udp_members :
    Each (fun p => p ∈ rawChecks model declaredTimers) TCPIPUDPDeliver.firings :=
  TCPIPUDPDeliver.members

theorem endpoint_send_member : (rule_238, none) ∈ rawChecks model declaredTimers :=
  TCPIPSendQueue.member

#print axioms endpoint_send_member
#print axioms endpoint_udp_members
#print axioms endpoint_arp_members

theorem endpoint_query_retry_obligation : (rule_3, some 1) ∈ rawChecks model declaredTimers :=
  TCPIPTimerRules.query_retry_obligation

#print axioms endpoint_query_retry_obligation
#print axioms endpoint_reset_count
#print axioms endpoint_preservation_count
#print axioms endpoint_preservation_unique
#print axioms endpoint_preservation_checked

set_option maxRecDepth 16384 in
theorem frame_group : Approved.conflict_4 := by
  apply TCPIPFrameCatalog.conflict_of_catalog model conflictGroup_4
    (TCPIPFramePairs.control ++ TCPIPFramePairs.data)
  · decide +kernel
  · exact frameCatalogExact
  · exact fun p member =>
      (each_append TCPIPFramePairs.controlMembers TCPIPFramePairs.dataMembers).of_mem member
  · exact each_append TCPIPFramePairs.controlDisjoint TCPIPFramePairs.dataDisjoint

private theorem false_or_false {a b : Bool} (impossible : a = true → b = true → False) :
    a = false ∨ b = false := by
  cases a <;> cases b <;> simp_all

private theorem emptySend (s : Snapshot) (f : Values)
    (h : TypedMachine.eval s f rule_239.guard = true) : TypedMachine.eval s f e52 = 0 := by
  change (TypedMachine.eval s f e923 && decide (TypedMachine.eval s f e52 = 0)) = true at h
  simp only [Bool.and_eq_true] at h
  exact of_decide_eq_true h.2

private theorem fullSend (s : Snapshot) (f : Values)
    (h : TypedMachine.eval s f rule_240.guard = true) : 17 ≤ TypedMachine.eval s f e1207 := by
  change (TypedMachine.eval s f e923 && decide (17 ≤ TypedMachine.eval s f e1207)) = true at h
  simp only [Bool.and_eq_true] at h
  exact of_decide_eq_true h.2

private theorem bufferedBound (s : Snapshot) (f : Values) (h : invariantsHold model s = true) :
    TypedMachine.eval s f e1206 ≤ 16 := by
  have bound : TypedMachine.eval s zeroValues e1691 = true :=
    List.all_eq_true.mp h e1691 (by rw [model_invariants]; simp)
  exact of_decide_eq_true bound

theorem send_group : Approved.conflict_15 := by
  apply conflict_from_residual
  have exactPairs : residualPairs conflictGroup_15 = [(rule_239, rule_240)] := rfl
  rw [exactPairs]
  constructor
  · intro s f valid _
    apply false_or_false
    intro a b
    have lower := fullSend s f b
    change 17 ≤ TypedMachine.eval s f e1206 + TypedMachine.eval s f e52 at lower
    rw [emptySend s f a, Int.add_zero] at lower
    exact (by decide : ¬ (17 : Int) ≤ 16) (Int.le_trans lower (bufferedBound s f valid))
  · trivial

#print axioms send_group

private theorem readyVsBlocked (s : Snapshot) (f : Values) {mode tail : Expr .boolean} :
    TypedMachine.eval s f (.boolAnd (.boolAnd e923 (.boolAnd e1225 mode)) tail) = false ∨
      TypedMachine.eval s f e1250 = false := by
  apply false_or_false
  intro ready blocked
  change ((TypedMachine.eval s f e923 &&
    ((true && TypedMachine.eval s f e1224) && TypedMachine.eval s f mode)) &&
      TypedMachine.eval s f tail) = true at ready
  change (TypedMachine.eval s f e923 && !(TypedMachine.eval s f e1224)) = true at blocked
  simp only [Bool.and_eq_true, Bool.true_and] at ready blocked
  have impossible := blocked.2
  rw [ready.1.2.1] at impossible
  contradiction

theorem transmit_group : Approved.conflict_16 := by
  apply conflict_from_residual
  have exactPairs : residualPairs conflictGroup_16 =
      [(rule_241, rule_247), (rule_242, rule_247), (rule_243, rule_247),
        (rule_244, rule_247), (rule_245, rule_247), (rule_246, rule_247)] := rfl
  rw [exactPairs]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  all_goals
    intro s f _ _
    exact readyVsBlocked s f

#print axioms transmit_group

#print axioms closed_groups
#print axioms frame_group

set_option maxRecDepth 16384 in
theorem endpoint_raw_exact : Approved.raw_catalog_exact := by rfl
set_option maxRecDepth 16384 in
theorem endpoint_raw_count : (rawChecks model declaredTimers).length = 335 := by
  rw [endpoint_raw_exact] <;> rfl

set_option maxRecDepth 16384 in
theorem endpoint_conflicts_exact : Approved.conflict_catalog_exact := by rfl
set_option maxRecDepth 16384 in
theorem endpoint_guards_disjoint : TypedContracts.GuardsDisjoint model := by
  apply disjoint_from_checks
  rw [endpoint_conflicts_exact]
  obtain ⟨g0, g1, g2, g3, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g17, _⟩ := closed_groups
  exact ⟨g0, g1, g2, g3, frame_group, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14,
    send_group, transmit_group, g17, trivial⟩

#print axioms endpoint_raw_exact
#print axioms endpoint_raw_count
#print axioms endpoint_conflicts_exact
#print axioms endpoint_guards_disjoint

end TCPIPAudit
