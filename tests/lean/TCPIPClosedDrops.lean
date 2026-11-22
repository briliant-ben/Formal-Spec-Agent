import TCPIPClosedCore
namespace TCPIPClosedTransitions
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts
open EffectConditions EffectFootprint TimedObligations TCPIPSendWire GuardedSuffix
set_option maxRecDepth 16384

def beforeControl (r : Rule) : Rule := {r with actions := r.actions.dropLast}

theorem retain_closed_with_queue_release (r : Rule) (select : Expr .boolean)
    (guard : r.guard = controlGuard (fixedText e14) (some select))
    (actions : r.actions = r.actions.dropLast ++ [.assign .text 56 e14])
    (untouched : r.actions.dropLast.all (ignoresAction (.variable .text 56)) = true)
    (total : obligationsFor (beforeControl r) none [] = [])
    (catalog : model.invariants.filter (fun inv => !ignoresFiring inv (beforeControl r) none) =
      TCPIPQueueRelease.queueClauses)
    (bind : TCPIPQueueRelease.queueClauses.map (fun inv => obligationsFor (beforeControl r) none [inv]) =
      TCPIPQueueRelease.queueClauses.map (fun inv => [ExprRewrite.run TCPIPQueueRelease.releaseReads inv])) :
    FiringPreserves model r none := by
  apply preserves_after_removing_text model r none r.actions.dropLast 56 (fixedText e14) actions untouched
  · intro s f enabled
    rw [guard] at enabled
    change ((decide (TypedMachine.eval s f e488 = fixedText e14) && TypedMachine.eval s f select) &&
      TypedMachine.eval s f e721) = true at enabled
    simp only [Bool.and_eq_true] at enabled
    exact of_decide_eq_true enabled.1.1
  · change FiringPreserves model (beforeControl r) none
    apply preserves_touched
    intro s f valid _ _
    refine ⟨total.symm ▸ rfl, ?_⟩
    intro inv member seen
    have queue : inv ∈ TCPIPQueueRelease.queueClauses := by
      rw [← catalog]
      exact List.mem_filter.mpr ⟨member, by simp [seen]⟩
    rw [List.map_inj_left.mp bind inv queue]
    change (TypedMachine.eval s f (ExprRewrite.run TCPIPQueueRelease.releaseReads inv) && true) = true
    simp [(TCPIPQueueRelease.release_queue_safe s f valid).of_mem queue]

theorem ignore_reset_closed : Approved.raw_193_external :=
  retain_closed_with_queue_release rule_193 e1078 rfl rfl (by decide +kernel) rfl rfl rfl

theorem ignore_reset_ack_closed : Approved.raw_205_external :=
  retain_closed_with_queue_release rule_205 e1115 rfl rfl (by decide +kernel) rfl rfl rfl

theorem drop_short_closed : Approved.raw_279_external :=
  retain_closed_with_queue_release rule_279 e1429 rfl rfl (by decide +kernel) rfl rfl rfl

theorem drop_ip_length_closed : Approved.raw_280_external :=
  retain_closed_with_queue_release rule_280 e1434 rfl rfl (by decide +kernel) rfl rfl rfl

theorem drop_ip_checksum_closed : Approved.raw_281_external :=
  retain_closed_with_queue_release rule_281 e1438 rfl rfl (by decide +kernel) rfl rfl rfl

theorem drop_tcp_length_closed : Approved.raw_282_external :=
  retain_closed_with_queue_release rule_282 e1447 rfl rfl (by decide +kernel) rfl rfl rfl

theorem drop_tcp_checksum_closed : Approved.raw_283_external :=
  retain_closed_with_queue_release rule_283 e1452 rfl rfl (by decide +kernel) rfl rfl rfl


end TCPIPClosedTransitions
