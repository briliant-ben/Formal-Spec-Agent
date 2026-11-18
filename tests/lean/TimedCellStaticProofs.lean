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

#print axioms initial_valid_checked
#print axioms initial_declared_checked
#print axioms rule_ids_checked
#print axioms arms_declared_checked
#print axioms coverage_checked
