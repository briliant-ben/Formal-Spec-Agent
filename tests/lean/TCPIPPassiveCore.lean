import TCPIPClosedCore
namespace TCPIPClosedTransitions
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts
open EffectConditions EffectFootprint TimedObligations TCPIPSendWire GuardedSuffix
set_option maxRecDepth 16384

theorem enter_listen (r : Rule) (start : String) (frameFilter : Option (Expr .boolean))
    (guard : r.guard = controlGuard start frameFilter)
    (different : start ≠ fixedText e807)
    (total : obligationsFor r none [] = [])
    (catalog : model.invariants.filter (fun inv => !ignoresFiring inv r none) =
      phaseClauses ++ [e1698, e1704, e1716])
    (statics : ∀ s f, (staticClauses false).all (fun inv => holds (obligationsFor r none [inv]) s f) = true)
    (buffer : obligationsFor r none [e1698] = [.implies (.boolNot (.equal .text e579 e807)) e935]) :
    FiringPreserves model r none := by
  apply preserves_touched
  intro s f valid _ enabled
  refine ⟨total.symm ▸ rfl, ?_⟩
  intro inv member seen
  have included : inv ∈ phaseClauses ++ [e1698, e1704, e1716] := by
    rw [← catalog]
    exact List.mem_filter.mpr ⟨member, by simp [seen]⟩
  have relevant : inv ∈ staticClauses false ∨ inv = e1698 := by
    simpa only [staticClauses, Bool.false_eq_true, ite_false, List.append_nil, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false, or_assoc, or_left_comm, or_comm] using included
  rcases relevant with static | rfl
  · exact List.all_eq_true.mp (statics s f) _ static
  · rw [guard] at enabled
    rw [buffer]
    change (TypedMachine.eval s f e935 && true) = true
    simp [empty_before s f start frameFilter different enabled valid]

theorem open_passive : Approved.raw_67_external :=
  enter_listen rule_67 (fixedText e14) none rfl (by decide) rfl rfl (fun _ _ => rfl) rfl

theorem reset_passive : Approved.raw_196_external :=
  enter_listen rule_196 (fixedText e740) (some e1088) rfl (by decide) rfl rfl (fun _ _ => rfl) rfl

theorem reset_ack_passive : Approved.raw_208_external :=
  enter_listen rule_208 (fixedText e740) (some e1123) rfl (by decide) rfl rfl (fun _ _ => rfl) rfl


end TCPIPClosedTransitions
