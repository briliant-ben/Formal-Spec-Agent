import Approved

namespace TimedProof
open Approved FormalSpecAgent TypedMachine TypedIR
open TypedContracts TypedFiringContracts BatchTotality TimedObligations

private theorem initial_valid_checked : TypedContracts.InitialValid model initial := by rfl

private theorem initial_declared_checked : TimerDomain.Declared declaredTimers initial := by
  intro entry member
  change entry ∈ ([] : List TimerEntry) at member
  simp at member

theorem initial : Approved.initial_admitted :=
  ⟨initial_valid_checked, by decide, initial_declared_checked, by rfl⟩

private theorem rule_ids_checked : rule_ids_unique := by unfold rule_ids_unique; decide

private theorem arms_declared_checked : arms_declared := by
  intro rule member timer delay arm
  rw [model_rules] at member
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;>
    simp_all [declaredTimers, rule_0, rule_1, rule_2, rule_3, rule_4]

private theorem coverage_checked : timer_coverage := by
  intro s _ valid entry inside known
  have id : entry.timer = 0 := List.mem_singleton.mp known
  have active : 0 ∈ s.timers.map TimerEntry.timer :=
    List.mem_map.mpr ⟨entry, inside, id⟩
  have holds : FormalSpecAgent.TypedMachine.eval s zeroValues e30 = true :=
    List.all_eq_true.mp valid e30 (by rw [model_invariants]; simp)
  have hot : s.state = 1 := by
    simpa [TypedMachine.eval, context, e30, e28, e29, TypedIR.eval, TypedIR.equalValue, active] using holds
  refine ⟨rule_4, ?_, hot.symm, ?_, ?_⟩
  · rw [model_rules]; simp
  · rw [id]; rfl
  · rfl

private theorem targets_declared_checked : targets_declared := by
  intro rule member
  rw [model_rules] at member
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;>
    simp [declaredStates, rule_0, rule_1, rule_2, rule_3, rule_4]

private theorem expiry_removed (s : Snapshot) :
    0 ∉ (cancelTimer s 0).timers.map TimerEntry.timer := by
  intro active
  obtain ⟨entry, member, eq⟩ := List.mem_map.mp active
  have rejected := (List.mem_filter.mp member).2
  simp [eq] at rejected

private theorem expiry_raw_checked : raw_4_timer_0 := by
  intro s fields _ _ _
  refine ⟨_, rfl, ?_⟩
  simp [invariantsHold, model_invariants, rule_4, withoutFiring,
    TypedMachine.eval, context, TypedIR.eval, TypedIR.equalValue, getValue, setValue,
    e0, e1, e3, e4, e13, e14, e20, e22, e25, e26, e27, e28, e29, e30,
    e31, e32, e33, e34, e35, e10, expiry_removed]

private theorem accepted_raw (r : Rule) (actions : r.actions = rule_0.actions)
    (target : r.target = 1) (guard : r.guard = e12) :
    FiringPreserves model r none := by
  intro s fields _ _ enabledGuard
  have small : ((fields.buffers 0).length : Int) ≤ 16 := by
    rw [guard] at enabledGuard
    change (TypedMachine.eval s fields e7 && decide (((fields.buffers 0).length : Int) ≤ 16)) = true at enabledGuard
    simp only [Bool.and_eq_true, decide_eq_true_eq] at enabledGuard
    exact enabledGuard.2
  unfold candidate
  rw [actions, target]
  simp [rule_0, withoutFiring, work, armTimer, invariantsHold, model_invariants,
    TypedMachine.eval, context, TypedIR.eval, equalValue, getValue, setValue,
    e1, e8, e10, e13, e14, e19, e20, e25, e26, e27, e28, e29, e30, e31,
    e35, small]

private theorem rejected_raw (r : Rule) (actions : r.actions = rule_1.actions ∨
    r.actions = rule_3.actions) (selfLoop : r.target = r.source) :
    FiringPreserves model r none := by
  intro s fields invariant atSource _
  unfold candidate
  rw [selfLoop, ← atSource]
  rcases actions with actions | actions
  all_goals
    rw [actions]
    refine ⟨_, rfl, ?_⟩
    exact invariant

private theorem raw_catalog_checked : raw_catalog_exact := by rfl

private theorem conflict_catalog_checked : conflict_catalog_exact := by rfl

theorem preservation : Each (fun p => FiringPreserves model p.1 p.2)
    (rawChecks model declaredTimers) := by
  have exactCatalog : rawChecks model declaredTimers = rawCatalog := raw_catalog_checked
  rw [exactCatalog]
  exact ⟨accepted_raw rule_0 rfl rfl rfl, rejected_raw rule_1 (Or.inl rfl) rfl,
    accepted_raw rule_2 rfl rfl rfl, rejected_raw rule_3 (Or.inr rfl) rfl,
    expiry_raw_checked, trivial⟩

private theorem complement (s : Snapshot) (fields : Values) :
    TypedMachine.eval s fields e12 = false ∨ TypedMachine.eval s fields e24 = false := by
  have opposite : TypedMachine.eval s fields e24 = !(TypedMachine.eval s fields e12) := rfl
  rw [opposite]
  cases TypedMachine.eval s fields e12 <;> simp

private theorem conflicts_checked : Each (ConflictFree model) (conflictChecks model) := by
  have exactCatalog : conflictChecks model = conflictCatalog := conflict_catalog_checked
  rw [exactCatalog]
  constructor
  · intro s fields _ left leftIn right rightIn distinct _
    simp [conflictGroup_0] at leftIn rightIn
    rcases leftIn with rfl | rfl <;> rcases rightIn with rfl | rfl
    · exact (distinct rfl).elim
    · exact complement s fields
    · exact Or.symm (complement s fields)
    · exact (distinct rfl).elim
  constructor
  · intro s fields _ left leftIn right rightIn distinct _
    simp [conflictGroup_1] at leftIn rightIn
    rcases leftIn with rfl | rfl <;> rcases rightIn with rfl | rfl
    · exact (distinct rfl).elim
    · exact complement s fields
    · exact Or.symm (complement s fields)
    · exact (distinct rfl).elim
  constructor
  · intro _ _ _ left leftIn right rightIn distinct _
    simp [conflictGroup_2] at leftIn rightIn
    exact (distinct (congrArg Rule.id (leftIn.trans rightIn.symm))).elim
  · trivial

theorem timers : TimerContracts model declaredStates declaredTimers :=
  timer_contracts_from_checks model declaredStates declaredTimers targets_declared_checked
    arms_declared_checked rule_ids_checked coverage_checked preservation conflicts_checked

end TimedProof
