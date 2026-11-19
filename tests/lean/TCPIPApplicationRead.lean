import Approved
import EffectConditions
import GuardedSuffix

namespace TCPIPApplicationRead
set_option maxRecDepth 16384
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts
open EffectConditions EffectFootprint GuardedSuffix TimedObligations

private def shortened : Rule := {rule_278 with actions := rule_278.actions.dropLast}

private theorem control (s : Snapshot) (f : Values) (link : Expr .boolean)
    (enabled : TypedMachine.eval s f (.boolAnd e1423 link) = true) :
    TypedMachine.eval s f e923 = true := by
  change ((TypedMachine.eval s f e923 && TypedMachine.eval s f e1422) &&
    TypedMachine.eval s f link) = true at enabled
  simp only [Bool.and_eq_true] at enabled
  exact enabled.1.1

private theorem slice_bound (s : Snapshot) (f : Values)
    (valid : invariantsHold model s = true) :
    (Int.ofNat (TypedMachine.eval s f e1426).length) ≤ 16 := by
  have old := List.all_eq_true.mp valid e1692 (by rw [model_invariants]; simp)
  have capacity : Int.ofNat (TypedMachine.eval s f e932).length ≤ 16 := of_decide_eq_true old
  have sliceLen (data : Bytes) (offset count : Int) :
      (Int.ofNat (byteSlice data offset count).length) ≤ Int.ofNat data.length := by
    unfold byteSlice
    apply Int.ofNat_le.mpr
    rw [List.length_take, List.length_drop]
    exact Nat.le_trans (Nat.min_le_right ..) (Nat.sub_le ..)
  exact Int.le_trans (sliceLen _ _ _) capacity

theorem after_read (s : Snapshot) (f : Values)
    (valid : invariantsHold model s = true) (est : TypedMachine.eval s f e923 = true) :
    Each (fun inv => holds (obligationsFor shortened none [inv]) s f = true)
      [e1692, e1698, e1699, e1706] := by
  refine ⟨?_, ?_, ?_, rfl, trivial⟩
  · change (decide (Int.ofNat (TypedMachine.eval s f e1426).length ≤ 16) && true) = true
    rw [decide_eq_true (slice_bound s f valid)]
    rfl
  · change ((!(!TypedMachine.eval s f e923) || _) && true) = true
    simp [est]
  · let window := 16 - (Int.ofNat (TypedMachine.eval s f e1426).length)
    change (decide (window = window) && true) = true
    simp

private theorem link_guard (s : Snapshot) (f : Values) (link : Expr .boolean)
    (enabled : TypedMachine.eval s f (.boolAnd e1423 link) = true) :
    TypedMachine.eval s f link = true := by
  change (TypedMachine.eval s f e1423 && TypedMachine.eval s f link) = true at enabled
  simp only [Bool.and_eq_true] at enabled
  exact enabled.2

def cut (rule : Rule) : Rule := {rule with actions := rule.actions.dropLast}

theorem certify (rule : Rule) (link : Expr .boolean)
    (guardShape : rule.guard = .boolAnd e1423 link)
    (actions : rule.actions = rule.actions.dropLast ++ [.assign .text 56 e807])
    (untouched : rule.actions.dropLast.all (ignoresAction (.variable .text 56)) = true)
    (catalog : model.invariants.filter (fun inv => !ignoresFiring inv (cut rule) none) = affected)
    (total : ∀ s f, holds (obligationsFor (cut rule) none []) s f = true)
    (conditions : ∀ s f, invariantsHold model s = true → TypedMachine.eval s f e923 = true →
      TypedMachine.eval s f link = true →
      Each (fun inv => holds (obligationsFor (cut rule) none [inv]) s f = true) affected) :
    FiringPreserves model rule none := by
  apply preserves_after_removing_text model rule none rule.actions.dropLast 56
    (TypedMachine.eval initial zeroValues e807) actions untouched
  · intro s f enabled
    rw [guardShape] at enabled
    exact of_decide_eq_true (control s f link enabled)
  · change FiringPreserves model (cut rule) none
    apply preserves_touched
    intro s f valid _ enabled
    have atGuard : TypedMachine.eval s f (.boolAnd e1423 link) = true := guardShape ▸ enabled
    refine ⟨total s f, ?_⟩
    intro inv member seen
    apply (conditions s f valid (control s f link atGuard) (link_guard s f link atGuard)).of_mem
    rw [← catalog]
    exact List.mem_filter.mpr ⟨member, by simp [seen]⟩

theorem receive_resolved : Approved.raw_278_external := by
  apply certify rule_278 e38 rfl rfl (by decide +kernel) rfl (fun _ _ => rfl)
  intro s f valid est _
  exact after_read s f valid est

set_option maxHeartbeats 1600000 in
theorem receive_pending : Approved.raw_277_external := by
  apply certify rule_277 e35 rfl rfl (by decide +kernel) rfl (fun _ _ => rfl)
  intro s f valid est pending
  have read := after_read s f valid est
  refine ⟨rfl, ?_, rfl, read.1, read.2.1, read.2.2.1, read.2.2.2.1, rfl, trivial⟩
  change (TypedMachine.eval s f e35 && true) = true
  simp [pending]

#print axioms receive_pending
#print axioms receive_resolved

end TCPIPApplicationRead
