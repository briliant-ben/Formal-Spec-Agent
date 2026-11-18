import Approved

open FormalSpecAgent FormalSpecAgent.TypedMachine FormalSpecAgent.TypedIR
open Approved

theorem initial_valid_checked : timed_initial_valid := by rfl

theorem initial_declared_checked : timed_initial_declared := by
  intro entry member
  change entry ∈ ([] : List TimerEntry) at member
  simp at member

theorem rule_ids_checked : timed_rule_ids_unique := by unfold timed_rule_ids_unique; decide

theorem arms_declared_checked : timed_arms_declared := by
  intro rule member timer delay arm
  rw [model_rules] at member
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;>
    simp_all [rule_0, rule_1, rule_2, rule_3, rule_4]

theorem coverage_checked : timed_covers_timers := by
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

theorem targets_declared_checked : timed_targets_declared := by
  intro rule member
  rw [model_rules] at member
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;>
    simp [rule_0, rule_1, rule_2, rule_3, rule_4]

#print axioms initial_valid_checked
#print axioms initial_declared_checked
#print axioms rule_ids_checked
#print axioms arms_declared_checked
#print axioms coverage_checked
#print axioms targets_declared_checked

open TypedContracts TypedFiringContracts BatchTotality

private theorem expiry_removed (s : Snapshot) :
    0 ∉ (cancelTimer s 0).timers.map TimerEntry.timer := by
  intro active
  obtain ⟨entry, member, eq⟩ := List.mem_map.mp active
  have rejected := (List.mem_filter.mp member).2
  simp [eq] at rejected

theorem expiry_raw_checked : FiringPreserves model rule_4 (some 0) := by
  intro s fields _ _ _
  refine ⟨_, rfl, ?_⟩
  simp [invariantsHold, model_invariants, rule_4, withoutFiring,
    TypedMachine.eval, context, TypedIR.eval, TypedIR.equalValue, getValue, setValue,
    e0, e1, e3, e4, e13, e14, e20, e22, e25, e26, e27, e28, e29, e30,
    e31, e32, e33, e34, e35, e10, expiry_removed]

theorem external_coverage_checked : Covers model [0, 1] := by
  intro s event fields state allowed _
  rw [model_external_events] at allowed
  have eventZero := List.mem_singleton.mp allowed
  subst event
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at state
  cases decision : TypedMachine.eval s fields e12
  · rcases state with cold | hot
    · exact ⟨rule_1, by rw [model_rules]; simp, cold.symm, rfl, by
        change !(TypedMachine.eval s fields e12) = true
        simp [decision]⟩
    · exact ⟨rule_3, by rw [model_rules]; simp, hot.symm, rfl, by
        change !(TypedMachine.eval s fields e12) = true
        simp [decision]⟩
  · rcases state with cold | hot
    · exact ⟨rule_0, by rw [model_rules]; simp, cold.symm, rfl, decision⟩
    · exact ⟨rule_2, by rw [model_rules]; simp, hot.symm, rfl, decision⟩

#print axioms expiry_raw_checked
#print axioms external_coverage_checked

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

theorem external_raw_checked : ∀ event ∈ model.externalEvents,
    ScheduledPreservation.MatchingRaw model event none := by
  intro event allowed rule member trigger
  rw [model_external_events] at allowed
  have eventZero := List.mem_singleton.mp allowed
  subst event
  rw [model_rules] at member
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact accepted_raw rule_0 rfl rfl rfl
  · exact rejected_raw rule_1 (Or.inl rfl) rfl
  · exact accepted_raw rule_2 rfl rfl rfl
  · exact rejected_raw rule_3 (Or.inr rfl) rfl
  · contradiction

theorem timer_raw_checked : BatchPreservation.TimerRaw [0] model := by
  intro timer known rule member trigger
  have timerZero := List.mem_singleton.mp known
  subst timer
  rw [model_rules] at member
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · contradiction
  · contradiction
  · contradiction
  · contradiction
  · exact expiry_raw_checked

#print axioms external_raw_checked
#print axioms timer_raw_checked

theorem guards_disjoint_checked : GuardsDisjoint model := by
  intro s fields _ event left right leftMember rightMember distinct leftSource rightSource
    leftEvent rightEvent
  rw [model_rules] at leftMember rightMember
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at leftMember rightMember
  rcases leftMember with rfl | rfl | rfl | rfl | rfl <;>
    rcases rightMember with rfl | rfl | rfl | rfl | rfl <;>
    simp only [rule_0, rule_1, rule_2, rule_3, rule_4] at distinct leftSource rightSource leftEvent rightEvent ⊢ <;>
    try omega
  all_goals
    have complement : TypedMachine.eval s fields e24 = !(TypedMachine.eval s fields e12) := rfl
    rw [complement]
    cases TypedMachine.eval s fields e12 <;> simp

theorem timed_cell_contracts : Contracts model [0, 1] [0] :=
  ⟨targets_declared_checked, arms_declared_checked, rule_ids_checked,
    guards_disjoint_checked, coverage_checked, timer_raw_checked,
    external_coverage_checked, external_raw_checked⟩

theorem timed_cell_start : Admitted model [0, 1] [0] initial :=
  ⟨initial_valid_checked, by decide, initial_declared_checked, by rfl⟩

/-- Concrete use of the generic theorem on the model generated from the IR.
    Fields are arbitrary typed values, with no cap imposed by this theorem. -/
theorem timed_cell_initial_dispatch (limit : Int) (fields : Values) (bound : 0 ≤ limit) :
    ∃ batch, BatchMachine.dispatch model initial 0 fields limit = .ok batch ∧
      Admitted model [0, 1] [0] batch.after ∧ batch.after.now = limit ∧
      BatchPreservation.Preserved [0] model batch :=
  dispatch_total model [0, 1] [0] limit timed_cell_contracts initial timed_cell_start bound
    0 fields (by rw [model_external_events]; simp)

#print axioms guards_disjoint_checked
#print axioms timed_cell_contracts
#print axioms timed_cell_start
#print axioms timed_cell_initial_dispatch
