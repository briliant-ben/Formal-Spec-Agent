import Approved
import EffectConditions

namespace TimedProof
open Approved FormalSpecAgent TypedMachine TypedIR BatchTotality
open TimedObligations TypedFiringContracts EffectConditions

theorem initial : Approved.initial_admitted := by
  refine ⟨rfl, by decide, ?_, ?_⟩
  · intro entry member
    cases member
  · apply (TimerRank.wellTimed_iff Approved.initial).mpr
    intro entry member
    cases member

private theorem publication : raw_0_external := by
  intro s fields _ _ enabled
  refine ⟨_, rfl, ?_⟩
  change (decide (((fields.buffers 0).length : Int) ≤ 8) && true) = true
  change decide (((fields.buffers 0).length : Int) ≤ 8) = true at enabled
  simp [enabled]

private theorem clear : raw_1_external := by
  intro s fields _ _ _
  exact ⟨_, rfl, rfl⟩

theorem preservation : Each (fun p => FiringPreserves model p.1 p.2)
    (rawChecks model declaredTimers) := ⟨publication, clear, trivial⟩

private theorem target_states : targets_declared := by
  intro r member
  rw [model_rules] at member
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl <;> decide

private theorem arm_ids : arms_declared := by
  intro r member timer delay armed
  rw [model_rules] at member
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl <;> simp [rule_0, rule_1] at armed

private theorem coverage : timer_coverage := by
  intro s _ _ entry _ known
  cases known

private theorem conflicts : Each (ConflictFree model) (conflictChecks model) := by
  change Each (ConflictFree model) [[rule_0], [rule_1]]
  refine ⟨?_, ?_, trivial⟩
  all_goals
    intro s fields valid left leftIn right rightIn distinct source
    cases List.mem_singleton.mp leftIn
    cases List.mem_singleton.mp rightIn
    exact (distinct rfl).elim

theorem timers : TimerContracts model declaredStates declaredTimers :=
  timer_contracts_from_checks model declaredStates declaredTimers target_states arm_ids
    (by decide) coverage preservation conflicts

end TimedProof
