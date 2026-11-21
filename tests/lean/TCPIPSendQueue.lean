import Approved
import EffectConditions
import GuardedSuffix

namespace TCPIPSendQueue

open Approved FormalSpecAgent FormalSpecAgent.TypedMachine FormalSpecAgent.TypedIR
open EffectConditions EffectFootprint GuardedSuffix TypedFiringContracts TimedObligations

private def prefixActions := rule_238.actions.dropLast
private def queued : Rule := { rule_238 with actions := prefixActions }

private theorem capacityGuard (s : Snapshot) (f : Values)
    (guard : TypedMachine.eval s f rule_238.guard = true) :
    TypedMachine.eval s f e923 = true ∧ TypedMachine.eval s f e1208 = true := by
  change (TypedMachine.eval s f e923 && (TypedMachine.eval s f e1205 &&
    TypedMachine.eval s f e1208)) = true at guard
  simp only [Bool.and_eq_true] at guard
  exact ⟨guard.1, guard.2.2⟩

private theorem shorter : FiringPreserves model queued none := by
  apply preserves_touched
  intro s f _ _ guard
  obtain ⟨established, capacity⟩ := capacityGuard s f guard
  refine ⟨rfl, ?_⟩
  intro inv member observed
  have catalog : model.invariants.filter (fun entry => !ignoresFiring entry queued none) =
      [e1691, e1698] := rfl
  have affected : inv ∈ model.invariants.filter (fun entry => !ignoresFiring entry queued none) :=
    List.mem_filter.mpr ⟨member, by simp [observed]⟩
  rw [catalog] at affected
  simp only [List.mem_cons, List.not_mem_nil, or_false] at affected
  rcases affected with same | same <;> subst inv
  · have nextBound : TypedMachine.eval s f e925 + TypedMachine.eval s f e929 +
        TypedMachine.eval s f e52 ≤ 16 := of_decide_eq_true capacity
    change ((decide ((Int.ofNat (TypedMachine.eval s f e1211).length) +
      TypedMachine.eval s f e929 ≤ 16)) && true) = true
    have appendBound :
        Int.ofNat (TypedMachine.eval s f e1211).length = TypedMachine.eval s f e925 +
          TypedMachine.eval s f e52 := by
      change Int.ofNat ((TypedMachine.eval s f e924) ++ (TypedMachine.eval s f e17)).length =
        Int.ofNat (TypedMachine.eval s f e924).length + Int.ofNat (TypedMachine.eval s f e17).length
      rw [List.length_append]
      exact Int.natCast_add ..
    rw [appendBound, Int.add_right_comm, decide_eq_true nextBound]
    rfl
  · change ((!(!TypedMachine.eval s f e923) || _) && true) = true
    simp [established]

theorem send_queue : Approved.raw_238_external := by
  apply preserves_after_removing_text model rule_238 none prefixActions 56
    (TypedMachine.eval initial zeroValues e807)
  · rfl
  · decide +kernel
  · intro s f guard
    exact of_decide_eq_true (capacityGuard s f guard).1
  · exact shorter

theorem member : (rule_238, none) ∈ rawChecks model declaredTimers :=
  raw_external_member model declaredTimers rule_238 (List.mem_iff_getElem?.mpr ⟨238, rfl⟩)
    (by decide)

#print axioms send_queue
end TCPIPSendQueue
