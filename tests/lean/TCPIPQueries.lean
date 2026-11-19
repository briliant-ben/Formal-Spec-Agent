import Approved
import EffectConditions

namespace TCPIPQueries
open Approved FormalSpecAgent FormalSpecAgent.TypedIR FormalSpecAgent.TypedMachine
open EffectConditions TypedFiringContracts TimedObligations

private def earlier := model.invariants.drop 4 |>.take 4
private def middle := model.invariants.drop 9 |>.take 5
private def later := model.invariants.drop 15

set_option maxRecDepth 16384 in
private theorem invariantPartition :
    model.invariants = [e1594,e1597,e1601,e1604] ++ earlier ++ [e1614] ++ middle ++ [e1628] ++ later := rfl

set_option maxRecDepth 16384 in
private theorem unaffected :
    ∀ inv ∈ earlier ++ middle ++ later, obligationsFor rule_4 (some 0) [inv] = atTarget 0 [inv] := by
  apply List.map_inj_left.mp
  rfl

private def ordinaryTouched := [e1594,e1597,e1601,e1604,e1614,e1628]

private theorem unchanged_condition (s : Snapshot) (f : Values) (state : s.state = 0)
    (valid : invariantsHold model s = true) (rule : Rule) (firing : Option Nat)
    (same : ∀ inv ∈ earlier ++ middle ++ later, obligationsFor rule firing [inv] = atTarget 0 [inv]) :
    ∀ inv ∈ earlier ++ middle ++ later, inv ∈ model.invariants →
      holds (obligationsFor rule firing [inv]) s f = true := by
  intro inv found member
  rw [same inv found, ← state, holds_atCurrent]
  simpa [holds] using List.all_eq_true.mp valid inv member

private theorem ordinary_conditions (s : Snapshot) (f : Values)
    (rule : Rule) (firing : Option Nat)
    (unchanged : ∀ inv ∈ earlier ++ middle ++ later, inv ∈ model.invariants →
      holds (obligationsFor rule firing [inv]) s f = true)
    (changed : Each (fun inv => holds (obligationsFor rule firing [inv]) s f = true) ordinaryTouched) :
    ∀ inv ∈ model.invariants, holds (obligationsFor rule firing [inv]) s f = true := by
  intro inv member
  have cases := member
  rw [invariantPartition] at cases
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at cases
  have untouched (found : inv ∈ earlier ++ middle ++ later) :
      holds (obligationsFor rule firing [inv]) s f = true := by
    exact unchanged inv found member
  rcases cases with (((((firstTouched | first) | queue) | second) | domain) | third)
  · apply changed.of_mem
    simp only [ordinaryTouched, List.mem_cons, List.not_mem_nil, or_false]
    rcases firstTouched with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact untouched (List.mem_append_left _ (List.mem_append_left _ first))
  · exact changed.of_mem (by simp [ordinaryTouched, queue])
  · exact untouched (List.mem_append_left _ (List.mem_append_right _ second))
  · exact changed.of_mem (by simp [ordinaryTouched, domain])
  · exact untouched (List.mem_append_right _ third)

private theorem before_cache_expiry (s : Snapshot) (f : Values)
    (valid : invariantsHold model s = true) (resolved : TypedMachine.eval s zeroValues e38 = true) :
    TypedMachine.eval s f e1589 = true ∧ TypedMachine.eval s f e1613 = false := by
  have phase := List.all_eq_true.mp valid e1601 (by rw [model_invariants]; simp)
  change (!TypedMachine.eval s zeroValues e38 || TypedMachine.eval s zeroValues e1600) = true at phase
  simp only [resolved, Bool.not_true, Bool.false_or] at phase
  change ((TypedMachine.eval s zeroValues e1598 && TypedMachine.eval s zeroValues e1589) &&
    TypedMachine.eval s zeroValues e1591) = true at phase
  simp only [Bool.and_eq_true] at phase
  refine ⟨phase.1.2, ?_⟩
  have state : TypedMachine.eval s zeroValues e15 = TypedMachine.eval s zeroValues e37 :=
    of_decide_eq_true resolved
  have pending : TypedMachine.eval s zeroValues e35 = false := by
    change decide (TypedMachine.eval s zeroValues e15 = TypedMachine.eval s zeroValues e34) = false
    rw [state]
    rfl
  have queued := List.all_eq_true.mp valid e1614 (by rw [model_invariants]; simp)
  change (!TypedMachine.eval s zeroValues e1613 || TypedMachine.eval s zeroValues e35) = true at queued
  rw [pending, Bool.or_false] at queued
  exact Bool.not_eq_true' _ ▸ queued

theorem cache_expiry : Approved.raw_4_timer_0 := by
  apply preserves_clauses
  intro s f valid source enabled
  have state : s.state = 0 := source
  change (TypedMachine.eval s f e38 && true) = true at enabled
  simp only [Bool.and_true] at enabled
  obtain ⟨queryInactive, unqueued⟩ := before_cache_expiry s f valid enabled
  refine ⟨rfl, ordinary_conditions s f _ _ (unchanged_condition s f state valid _ _ unaffected) ?_⟩
  refine ⟨?_, rfl, rfl, rfl, ?_, rfl, trivial⟩
  · change ((TypedMachine.eval s f e1589 && true) && true) = true
    simp [queryInactive]
  · change (((!TypedMachine.eval s f e1613) || false) && true) = true
    simp [unqueued]

private theorem pending_cache_inactive (s : Snapshot) (f : Values)
    (valid : invariantsHold model s = true) (pending : TypedMachine.eval s zeroValues e35 = true) :
    TypedMachine.eval s f e1592 = true := by
  have phase := List.all_eq_true.mp valid e1597 (by rw [model_invariants]; simp)
  change (!TypedMachine.eval s zeroValues e35 || TypedMachine.eval s zeroValues e1596) = true at phase
  simp only [pending, Bool.not_true, Bool.false_or] at phase
  change ((TypedMachine.eval s zeroValues e1587 && TypedMachine.eval s zeroValues e1588) &&
    TypedMachine.eval s zeroValues e1592) = true at phase
  simp only [Bool.and_eq_true] at phase
  exact phase.2

set_option maxRecDepth 16384 in
private theorem unaffectedUnqueued :
    ∀ inv ∈ earlier ++ middle ++ later, obligationsFor rule_26 (some 1) [inv] = atTarget 0 [inv] := by
  apply List.map_inj_left.mp
  rfl

theorem query_expiry_unqueued : Approved.raw_26_timer_1 := by
  apply preserves_clauses
  intro s f valid source enabled
  have state : s.state = 0 := source
  change (TypedMachine.eval s f e35 && (TypedMachine.eval s f e198 &&
    TypedMachine.eval s f e211)) = true at enabled
  simp only [Bool.and_eq_true] at enabled
  have cacheInactive := pending_cache_inactive s f valid enabled.1
  have left : TypedMachine.eval s f e200 = 0 := of_decide_eq_true enabled.2.2
  have noQueue : TypedMachine.eval s f e1613 = false := by
    change decide (1 ≤ TypedMachine.eval s f e200) = false
    rw [left]
    rfl
  refine ⟨rfl, ordinary_conditions s f _ _ (unchanged_condition s f state valid _ _ unaffectedUnqueued) ?_⟩
  refine ⟨?_, rfl, rfl, rfl, ?_, rfl, trivial⟩
  · change (TypedMachine.eval s f e1592 && true) = true
    simp [cacheInactive]
  · change (((!TypedMachine.eval s f e1613) || false) && true) = true
    simp [noQueue]

private def queuedEarlier := model.invariants.drop 4 |>.take 3
private def queuedMiddle := model.invariants.drop 10 |>.take 4
private def queuedLater := model.invariants.drop 15 |>.take 49

set_option maxRecDepth 16384 in
private theorem queuedPartition :
    model.invariants = [e1594,e1597,e1601,e1604] ++ queuedEarlier ++ [e1612,e1614,e1615] ++
      queuedMiddle ++ [e1628] ++ queuedLater ++ [e1721] := rfl

set_option maxRecDepth 16384 in
private theorem queuedUnaffected :
    ∀ inv ∈ queuedEarlier ++ queuedMiddle ++ queuedLater,
      obligationsFor rule_24 (some 1) [inv] = atTarget 0 [inv] := by
  apply List.map_inj_left.mp
  rfl

private theorem queued_conditions (s : Snapshot) (f : Values) (valid : invariantsHold model s = true)
    (state : s.state = 0) (pending : TypedMachine.eval s zeroValues e35 = true) :
    holds (obligationsFor rule_24 (some 1) []) s f = true ∧
    ∀ inv ∈ model.invariants, holds (obligationsFor rule_24 (some 1) [inv]) s f = true := by
  have cacheInactive := pending_cache_inactive s f valid pending
  refine ⟨rfl, ?_⟩
  intro inv member
  have cases := member
  rw [queuedPartition] at cases
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at cases
  rcases cases with ((((((changed | first) | cleared) | second) | domain) | third) | owner)
  · rcases changed with h | h | h | h <;> subst inv
    · change (TypedMachine.eval s f e1592 && true) = true
      simp [cacheInactive]
    · rfl
    · rfl
    · rfl
  · rw [queuedUnaffected inv (List.mem_append_left _ (List.mem_append_left _ first)),
      ← state, holds_atCurrent]
    simpa [holds] using List.all_eq_true.mp valid inv member
  · rcases cleared with h | h | h <;> subst inv <;> rfl
  · rw [queuedUnaffected inv (List.mem_append_left _ (List.mem_append_right _ second)),
      ← state, holds_atCurrent]
    simpa [holds] using List.all_eq_true.mp valid inv member
  · subst inv
    rfl
  · rw [queuedUnaffected inv (List.mem_append_right _ third), ← state, holds_atCurrent]
    simpa [holds] using List.all_eq_true.mp valid inv member
  · subst inv
    rfl

theorem query_expiry_udp : Approved.raw_24_timer_1 := by
  apply preserves_clauses
  intro s f valid source enabled
  change ((TypedMachine.eval s f e35 && TypedMachine.eval s f e202) &&
    TypedMachine.eval s f e205) = true at enabled
  simp only [Bool.and_eq_true] at enabled
  exact queued_conditions s f valid source enabled.1.1

theorem query_expiry_tcp : Approved.raw_25_timer_1 := by
  apply preserves_clauses
  intro s f valid source enabled
  change ((TypedMachine.eval s f e35 && TypedMachine.eval s f e202) &&
    TypedMachine.eval s f e209) = true at enabled
  simp only [Bool.and_eq_true] at enabled
  exact queued_conditions s f valid source enabled.1.1

private def queryDelay : Expr .boolean := .intGe e10 e44

set_option maxRecDepth 16384 in
private theorem unaffectedStart :
    ∀ inv ∈ earlier ++ middle ++ later, obligationsFor rule_0 none [inv] = queryDelay :: atTarget 0 [inv] := by
  apply List.map_inj_left.mp
  rfl

theorem query_start : Approved.raw_0_external := by
  apply preserves_clauses
  intro s f valid source enabled
  have state : s.state = 0 := source
  change (TypedMachine.eval s f e16 && TypedMachine.eval s f e19) = true at enabled
  simp only [Bool.and_eq_true] at enabled
  have empty : TypedMachine.eval s zeroValues e16 = true := enabled.1
  have phase := List.all_eq_true.mp valid e1594 (by rw [model_invariants]; simp)
  change (!TypedMachine.eval s zeroValues e16 || TypedMachine.eval s zeroValues e1593) = true at phase
  simp only [empty, Bool.not_true, Bool.false_or] at phase
  change ((TypedMachine.eval s zeroValues e1587 && TypedMachine.eval s zeroValues e1589) &&
    TypedMachine.eval s zeroValues e1592) = true at phase
  simp only [Bool.and_eq_true] at phase
  have mac : TypedMachine.eval s f e1587 = true := phase.1.1
  have cache : TypedMachine.eval s f e1592 = true := phase.2
  have untouched (inv : Expr .boolean) (found : inv ∈ earlier ++ middle ++ later)
      (member : inv ∈ model.invariants) : holds (obligationsFor rule_0 none [inv]) s f = true := by
    rw [unaffectedStart inv found]
    change holds (atTarget 0 [inv]) s f = true
    rw [← state, holds_atCurrent]
    simpa [holds] using List.all_eq_true.mp valid inv member
  refine ⟨rfl, ordinary_conditions s f _ _ untouched ?_⟩
  refine ⟨rfl, ?_, rfl, rfl, ?_, rfl, trivial⟩
  · change (((TypedMachine.eval s f e1587 && true) && TypedMachine.eval s f e1592) && true) = true
    simp [mac, cache]
  · change (((!TypedMachine.eval s f e1613) || true) && true) = true
    simp

def firings : List (Rule × Option Nat) :=
  [(rule_0, none), (rule_4, some 0), (rule_24, some 1), (rule_25, some 1), (rule_26, some 1)]

theorem checked : Each (fun p => FiringPreserves model p.1 p.2) firings :=
  ⟨query_start, cache_expiry, query_expiry_udp, query_expiry_tcp, query_expiry_unqueued, trivial⟩

private theorem timerMember (index : Nat) (rule : Rule) (owner : Nat)
    (selected : model.rules[index]? = some rule)
    (declared : owner ∈ declaredTimers) (eventMatches : rule.event = model.timerEvents owner) :
    (rule, some owner) ∈ rawChecks model declaredTimers :=
  raw_timer_member model declaredTimers rule owner (List.mem_iff_getElem?.mpr ⟨index, selected⟩)
    declared eventMatches

theorem members : Each (fun p => p ∈ rawChecks model declaredTimers) firings :=
  ⟨raw_external_member model declaredTimers rule_0 (List.mem_iff_getElem?.mpr ⟨0, rfl⟩)
      (by decide),
    timerMember 4 rule_4 0 rfl (by decide) rfl,
    timerMember 24 rule_24 1 rfl (by decide) rfl,
    timerMember 25 rule_25 1 rfl (by decide) rfl,
    timerMember 26 rule_26 1 rfl (by decide) rfl, trivial⟩

#print axioms query_start
#print axioms cache_expiry
#print axioms query_expiry_unqueued
#print axioms query_expiry_udp
#print axioms query_expiry_tcp
end TCPIPQueries
