import Approved
import InvariantFootprint
import TimerInvariantFacts

namespace TCPIPTimerRules

open FormalSpecAgent FormalSpecAgent.TypedIR FormalSpecAgent.TypedMachine
open FormalSpecAgent.TypedContracts FormalSpecAgent.TypedFiringContracts
open FormalSpecAgent.InvariantFootprint FormalSpecAgent.TimerInvariantFacts
open FormalSpecAgent.TimedObligations Approved

private theorem queryActive (s : Snapshot)
    (valid : invariantsHold model s = true) (pending : TypedMachine.eval s zeroValues e35 = true) :
    1 ∈ s.timers.map TimerEntry.timer := by
  have checked := List.all_eq_true.mp valid e1597 (by rw [model_invariants]; simp)
  change (!TypedMachine.eval s zeroValues e35 || TypedMachine.eval s zeroValues e1596) = true at checked
  simp only [pending, Bool.not_true, Bool.false_or] at checked
  change ((TypedMachine.eval s zeroValues e1587 && TypedMachine.eval s zeroValues e1588) &&
    TypedMachine.eval s zeroValues e1592) = true at checked
  simp only [Bool.and_eq_true] at checked
  exact of_decide_eq_true checked.1.2

private def setRetry (s : Snapshot) (value : Int) : Snapshot :=
  { s with values := setValue .integer 1 value s.values }

private theorem setRetry_preserves (s : Snapshot) (value : Int) (range : 0 ≤ value ∧ value ≤ 1)
    (valid : invariantsHold model s = true) : invariantsHold model (setRetry s value) = true := by
  have apart : ((model.invariants.take 3 ++ model.invariants.drop 4).all
      (ignoresSlot 1)) = true := by decide +kernel
  have splitInvariants : model.invariants = model.invariants.take 3 ++ e1604 :: model.invariants.drop 4 :=
    rfl
  apply List.all_eq_true.mpr
  intro inv member
  have splitMembership := member
  rw [splitInvariants] at splitMembership
  have either : inv = e1604 ∨ inv ∈ model.invariants.take 3 ++ model.invariants.drop 4 := by
    rcases List.mem_append.mp splitMembership with initial | suffix
    · exact Or.inr (List.mem_append_left _ initial)
    · rcases List.mem_cons.mp suffix with same | rest
      · exact Or.inl same
      · exact Or.inr (List.mem_append_right _ rest)
  rcases either with rfl | unaffected
  · change (decide (0 ≤ value) && decide (value ≤ 1)) = true
    simp [range.1, range.2]
  · exact (eval_after_unrelated_set inv (context s zeroValues) .integer 1 value
      (List.all_eq_true.mp apart inv unaffected)).trans (List.all_eq_true.mp valid inv member)

private def nextQuery (s : Snapshot) : Snapshot :=
  { s with timers := (cancelTimer s 1).timers ++ [⟨1, s.now + 1000⟩] }

private theorem retry_result (s : Snapshot) (f : Values)
    (control : getValue .text s.values 25 = TypedMachine.eval s f e34)
    (source : s.state = 0) :
    ∃ transition, candidate s rule_3 f rule_3.event (some 1) = .ok transition ∧
      transition.after = setRetry (nextQuery s) 1 := by
  let sent : Message := ⟨0, [⟨0, .octets, TypedMachine.eval (setRetry (cancelTimer s 1) 1) f e33⟩]⟩
  let updated := setRetry (nextQuery s) 1
  have same : getValue .text updated.values 25 = TypedMachine.eval s f e34 := control
  have updatedText : setValue .text 25 (TypedMachine.eval s f e34) updated.values = updated.values := by
    rw [← same]
    exact set_current_value .text 25 updated.values
  let transition : Transition := ⟨updated, 3, 3, f, [sent]⟩
  refine ⟨transition, ?_, rfl⟩
  have armResult : armTimer (setRetry (cancelTimer s 1) 1) 1 1000 = .ok updated := by
    simp [armTimer, updated, setRetry, nextQuery, cancelTimer, List.filter_filter]
  unfold candidate
  simp only [rule_3, withoutFiring, work]
  let finish (armed : Snapshot) : Transition :=
    { after := { armed with
                  values := setValue .text 25 (TypedMachine.eval s f e34) armed.values
                  state := 0 }
      rule := 3
      event := 3
      fields := f
      emitted := [sent] }
  change (match armTimer (setRetry (cancelTimer s 1) 1) 1 1000 with
    | .error fault => Except.error fault
    | .ok armed => Except.ok (finish armed)) = .ok transition
  rw [armResult]
  dsimp only [finish]
  rw [updatedText]
  have stateRestored (snapshot : Snapshot) (atTarget : snapshot.state = 0) :
      { snapshot with state := 0 } = snapshot := by
    cases snapshot
    simp_all
  rw [stateRestored updated source]

theorem query_retry : Approved.raw_3_timer_1 := by
  intro s f valid source guard
  change (TypedMachine.eval s f e35 && TypedMachine.eval s f e42) = true at guard
  simp only [Bool.and_eq_true] at guard
  have pending : TypedMachine.eval s zeroValues e35 = true := guard.1
  have control : getValue .text s.values 25 = TypedMachine.eval s f e34 :=
    of_decide_eq_true guard.1
  obtain ⟨transition, executed, after⟩ := retry_result s f control source
  have ready : invariantsHold model (nextQuery s) = true :=
    rearmed_invariants model s (nextQuery s) 1 1000 (queryActive s valid pending) (by simp [armTimer, nextQuery, cancelTimer, List.filter_filter]) valid
  exact ⟨transition, executed, after ▸ setRetry_preserves (nextQuery s) 1 (by decide) ready⟩

theorem query_retry_obligation : (rule_3, some 1) ∈ rawChecks model declaredTimers := by
  apply List.mem_flatMap.mpr
  refine ⟨rule_3, List.mem_iff_getElem?.mpr ⟨3, rfl⟩, List.mem_append.mpr (Or.inr ?_)⟩
  exact List.mem_filterMap.mpr ⟨1, by decide, rfl⟩

#print axioms query_retry
#print axioms query_retry_obligation

end TCPIPTimerRules
