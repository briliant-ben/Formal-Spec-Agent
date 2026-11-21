import TCPIPTimerCoverage
import TCPIPTimerRules
import TCPIPQueries
import TCPIPRetransmit
import TCPIPClosedTransitions

namespace TCPIPTimerContracts
open Approved FormalSpecAgent TypedMachine TypedIR BatchTotality
open TimerDomain TimedObligations TypedFiringContracts
set_option maxRecDepth 16384

private def targetsValid : Bool :=
  model.rules.all (fun r => declaredStates.contains r.target)

theorem targets : TargetsDeclared model declaredStates := by
  have checked : targetsValid = true := by decide +kernel
  intro r member
  exact List.contains_iff_mem.mp (List.all_eq_true.mp checked r member)

private def armsValid : Bool :=
  model.rules.all (fun r => r.actions.all fun a =>
    match a with
    | .arm id _ => declaredTimers.contains id
    | _ => true)

theorem arms : ArmsDeclared declaredTimers model := by
  have checked : armsValid = true := by decide +kernel
  intro r member timer delay armed
  exact List.contains_iff_mem.mp (List.all_eq_true.mp (List.all_eq_true.mp checked r member)
    (.arm timer delay) armed)

theorem unique : (model.rules.map Rule.id).Nodup := by decide +kernel

private def timerFirings : List (Rule × Option Nat) :=
  [(rule_3, some 1), (rule_4, some 0), (rule_24, some 1), (rule_25, some 1),
   (rule_26, some 1), (rule_150, some 2), (rule_151, some 2), (rule_152, some 2),
   (rule_153, some 2), (rule_154, some 2), (rule_155, some 2), (rule_156, some 2),
   (rule_157, some 2), (rule_158, some 2), (rule_159, some 2), (rule_160, some 2),
   (rule_161, some 2), (rule_162, some 2), (rule_163, some 2), (rule_164, some 2),
   (rule_165, some 4), (rule_166, some 4), (rule_167, some 4), (rule_168, some 4),
   (rule_169, some 4), (rule_170, some 4), (rule_171, some 3), (rule_258, some 2),
   (rule_259, some 2), (rule_260, some 2)]

theorem exact_catalog :
    (rawChecks model declaredTimers).filter (fun p => p.2.isSome) = timerFirings := rfl

theorem count : timerFirings.length = 30 := rfl

private theorem checked : Each (fun p => FiringPreserves model p.1 p.2) timerFirings :=
  ⟨TCPIPTimerRules.query_retry, TCPIPQueries.cache_expiry, TCPIPQueries.query_expiry_udp,
   TCPIPQueries.query_expiry_tcp, TCPIPQueries.query_expiry_unqueued, TCPIPRetransmit.syn_sent_empty,
   TCPIPRetransmit.syn_sent_pending, TCPIPRetransmit.syn_sent_resolved, TCPIPRetransmit.syn_received_empty,
   TCPIPRetransmit.syn_received_pending, TCPIPRetransmit.syn_received_resolved, TCPIPRetransmit.fin_wait_1_empty,
   TCPIPRetransmit.fin_wait_1_pending, TCPIPRetransmit.fin_wait_1_resolved, TCPIPRetransmit.closing_empty,
   TCPIPRetransmit.closing_pending, TCPIPRetransmit.closing_resolved, TCPIPRetransmit.last_ack_empty,
   TCPIPRetransmit.last_ack_pending, TCPIPRetransmit.last_ack_resolved, TCPIPClosedTransitions.close_165,
   TCPIPClosedTransitions.close_166, TCPIPClosedTransitions.close_167, TCPIPClosedTransitions.close_168,
   TCPIPClosedTransitions.close_169, TCPIPClosedTransitions.close_170, TCPIPClosedTransitions.close_171,
   TCPIPRetransmit.data_empty, TCPIPRetransmit.data_pending, TCPIPRetransmit.data_resolved,
   trivial⟩

theorem raw : BatchPreservation.TimerRaw declaredTimers model := by
  intro timer known r member trigger
  apply checked.of_mem (item := (r, some timer))
  rw [← exact_catalog]
  exact List.mem_filter.mpr ⟨raw_timer_member model declaredTimers r timer member known trigger, rfl⟩

theorem contract (disjoint : TypedContracts.GuardsDisjoint model) :
    TimerContracts model declaredStates declaredTimers :=
  ⟨targets, arms, unique, disjoint, TCPIPTimerCoverage.covered, raw⟩

end TCPIPTimerContracts
