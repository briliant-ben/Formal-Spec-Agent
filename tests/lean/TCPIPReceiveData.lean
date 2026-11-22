import TCPIPReceiveEffects

namespace TCPIPReceiveData
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts
open EffectConditions EffectFootprint GuardedSuffix TimedObligations
set_option maxRecDepth 16384

private theorem certify (overlap : Bool) (phase : LinkPhase)
    (guard : (rule overlap phase).guard = .boolAnd (dataGuard overlap) (linkGuard phase))
    (actions : (rule overlap phase).actions = prefixActions (rule overlap phase) ++ [.assign .text 56 e807])
    (untouched : (prefixActions (rule overlap phase)).all (ignoresAction (.variable .text 56)) = true)
    (catalog : model.invariants.filter (fun inv => !ignoresFiring inv (cut (rule overlap phase)) none) =
      affected phase)
    (total : ∀ s f, holds (obligationsFor (cut (rule overlap phase)) none []) s f = true) :
    FiringPreserves model (rule overlap phase) none := by
  apply preserves_after_removing_text model _ none (prefixActions (rule overlap phase)) 56
    (TypedMachine.eval initial zeroValues e807) actions untouched
  · intro s f enabled
    rw [guard] at enabled
    exact of_decide_eq_true (data_guard_facts s f overlap (both s f _ _ enabled).1).1
  · change FiringPreserves model (cut (rule overlap phase)) none
    apply preserves_touched
    intro s f valid _ enabled
    change TypedMachine.eval s f (rule overlap phase).guard = true at enabled
    rw [guard] at enabled
    obtain ⟨data, link⟩ := both s f _ _ enabled
    obtain ⟨est, room⟩ := data_guard_facts s f overlap data
    refine ⟨total s f, ?_⟩
    intro inv member seen
    apply (link_clauses s f overlap phase valid link est room).of_mem
    rw [← catalog]
    exact List.mem_filter.mpr ⟨member, by simp [seen]⟩

theorem in_order_empty : Approved.raw_261_external :=
  certify false .empty rfl rfl (by decide +kernel) rfl (fun _ _ => rfl)

theorem in_order_pending : Approved.raw_262_external :=
  certify false .pending rfl rfl (by decide +kernel) rfl (fun _ _ => rfl)

theorem in_order_resolved : Approved.raw_263_external :=
  certify false .resolved rfl rfl (by decide +kernel) rfl (fun _ _ => rfl)

theorem overlap_empty : Approved.raw_264_external :=
  certify true .empty rfl rfl (by decide +kernel) rfl (fun _ _ => rfl)

theorem overlap_pending : Approved.raw_265_external :=
  certify true .pending rfl rfl (by decide +kernel) rfl (fun _ _ => rfl)

theorem overlap_resolved : Approved.raw_266_external :=
  certify true .resolved rfl rfl (by decide +kernel) rfl (fun _ _ => rfl)

def firings : List (Rule × Option Nat) :=
  [(rule_261, none), (rule_262, none), (rule_263, none),
   (rule_264, none), (rule_265, none), (rule_266, none)]

theorem checked : Each (fun p => FiringPreserves model p.1 p.2) firings :=
  ⟨in_order_empty, in_order_pending, in_order_resolved, overlap_empty, overlap_pending,
   overlap_resolved, trivial⟩

private theorem receiveMember (index : Nat) (r : Rule)
    (selected : model.rules[index]? = some r) (external : r.event ∈ model.externalEvents) :
    (r, none) ∈ rawChecks model declaredTimers :=
  raw_external_member model declaredTimers r (List.mem_iff_getElem?.mpr ⟨index, selected⟩) external

theorem members : Each (fun p => p ∈ rawChecks model declaredTimers) firings :=
  ⟨receiveMember 261 rule_261 rfl (by decide), receiveMember 262 rule_262 rfl (by decide),
   receiveMember 263 rule_263 rfl (by decide), receiveMember 264 rule_264 rfl (by decide),
   receiveMember 265 rule_265 rfl (by decide), receiveMember 266 rule_266 rfl (by decide), trivial⟩

end TCPIPReceiveData
