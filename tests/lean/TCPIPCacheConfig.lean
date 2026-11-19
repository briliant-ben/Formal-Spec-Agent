import Approved
import EffectConditions

namespace TCPIPCacheConfig
open Approved FormalSpecAgent FormalSpecAgent.TypedIR FormalSpecAgent.TypedMachine
open EffectConditions TypedFiringContracts TimedObligations

private def earlier := [e1604]
private def middle := model.invariants.drop 5 |>.take 3
private def later := (model.invariants.drop 9 |>.take 5) ++ model.invariants.drop 15

set_option maxRecDepth 16384 in
private theorem invariantPartition :
    model.invariants = [e1594,e1597,e1601] ++ earlier ++ [e1607] ++ middle ++
      [e1614] ++ (model.invariants.drop 9 |>.take 5) ++ [e1628] ++ model.invariants.drop 15 := rfl

private def delayPositive : Expr .boolean := .intGe e46 e44

set_option maxRecDepth 16384 in
private theorem unaffected :
    ∀ inv ∈ (earlier ++ middle) ++ later,
      obligationsFor rule_13 none [inv] = delayPositive :: atTarget 0 [inv] := by
  apply List.map_inj_left.mp
  rfl

private def touched := [e1594,e1597,e1601,e1607,e1614,e1628]

private theorem config_clauses (rule : Rule) (s : Snapshot) (f : Values)
    (unchanged : ∀ inv ∈ (earlier ++ middle) ++ later, inv ∈ model.invariants →
      holds (obligationsFor rule none [inv]) s f = true)
    (checked : Each (fun inv => holds (obligationsFor rule none [inv]) s f = true) touched) :
    ∀ inv ∈ model.invariants, holds (obligationsFor rule none [inv]) s f = true := by
  intro inv member
  have classes := member
  rw [invariantPartition] at classes
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at classes
  rcases classes with (((((((phases | first) | ttl) | second) | queue) | third) | domain) | fourth)
  · apply checked.of_mem
    simp only [touched, List.mem_cons, List.not_mem_nil, or_false]
    rcases phases with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · exact unchanged inv (List.mem_append_left _ (List.mem_append_left _ first)) member
  · exact checked.of_mem (by simp [touched, ttl])
  · exact unchanged inv (List.mem_append_left _ (List.mem_append_right _ second)) member
  · exact checked.of_mem (by simp [touched, queue])
  · exact unchanged inv (List.mem_append_right _ (List.mem_append_left _ third)) member
  · exact checked.of_mem (by simp [touched, domain])
  · exact unchanged inv (List.mem_append_right _ (List.mem_append_right _ fourth)) member

private theorem implyEnabled (s : Snapshot) (premise tail : Expr .boolean)
    (implication : TypedMachine.eval s zeroValues (.implies premise tail) = true)
    (enabled : TypedMachine.eval s zeroValues premise = true) :
    TypedMachine.eval s zeroValues tail = true := by
  change (!TypedMachine.eval s zeroValues premise || TypedMachine.eval s zeroValues tail) = true
    at implication
  simpa only [enabled, Bool.not_true, Bool.false_or] using implication

private theorem no_queue (s : Snapshot) (valid : invariantsHold model s = true)
    (pending : TypedMachine.eval s zeroValues e35 = false) :
    TypedMachine.eval s zeroValues e1613 = false := by
  have queued := List.all_eq_true.mp valid e1614 (by rw [model_invariants]; simp)
  change (!TypedMachine.eval s zeroValues e1613 || TypedMachine.eval s zeroValues e35) = true at queued
  rw [pending, Bool.or_false] at queued
  exact Bool.not_eq_true' _ ▸ queued

private theorem cache_pre (s : Snapshot) (f : Values)
    (valid : invariantsHold model s = true) (resolved : TypedMachine.eval s zeroValues e38 = true) :
    TypedMachine.eval s f e1599 = true ∧ TypedMachine.eval s f e1613 = false := by
  have phase := implyEnabled s e38 e1600
    (List.all_eq_true.mp valid e1601 (by rw [model_invariants]; simp)) resolved
  change (TypedMachine.eval s zeroValues e1599 && TypedMachine.eval s zeroValues e1591) = true at phase
  simp only [Bool.and_eq_true] at phase
  have state : TypedMachine.eval s zeroValues e15 = TypedMachine.eval s zeroValues e37 :=
    of_decide_eq_true resolved
  have pending : TypedMachine.eval s zeroValues e35 = false := by
    change decide (TypedMachine.eval s zeroValues e15 = TypedMachine.eval s zeroValues e34) = false
    rw [state]
    rfl
  exact ⟨phase.1, no_queue s valid pending⟩

theorem config_resolved : Approved.raw_13_external := by
  apply preserves_clauses
  intro s f valid source enabled
  have state : s.state = 0 := source
  change (TypedMachine.eval s f e38 && TypedMachine.eval s f e50) = true at enabled
  simp only [Bool.and_eq_true] at enabled
  obtain ⟨phase, unqueued⟩ := cache_pre s f valid enabled.1
  have within : (decide (60000 ≤ f.integers 0) && decide (f.integers 0 ≤ 3600000)) = true := enabled.2
  simp only [Bool.and_eq_true] at within
  have lower : 60000 ≤ f.integers 0 := of_decide_eq_true within.1
  have delay : (decide (1 ≤ f.integers 0)) = true :=
    decide_eq_true (Int.le_trans (by decide : (1 : Int) ≤ 60000) lower)
  have untouched (inv : Expr .boolean) (found : inv ∈ (earlier ++ middle) ++ later)
      (member : inv ∈ model.invariants) : holds (obligationsFor rule_13 none [inv]) s f = true := by
    rw [unaffected inv found]
    change (decide (1 ≤ f.integers 0) && holds (atTarget 0 [inv]) s f) = true
    rw [delay, Bool.true_and, ← state, holds_atCurrent]
    simpa [holds] using List.all_eq_true.mp valid inv member
  refine ⟨?_, config_clauses _ s f untouched ?_⟩
  · change (decide (1 ≤ f.integers 0) && true) = true
    simp [delay]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · change (decide (1 ≤ f.integers 0) && true) = true
    simp [delay]
  · change (decide (1 ≤ f.integers 0) && true) = true
    simp [delay]
  · change (decide (1 ≤ f.integers 0) && ((TypedMachine.eval s f e1599 && true) && true)) = true
    simp [delay, phase]
  · change (decide (1 ≤ f.integers 0) && (TypedMachine.eval s f e50 && true)) = true
    simp [delay, enabled.2]
  · change (decide (1 ≤ f.integers 0) && (((!TypedMachine.eval s f e1613) || false) && true)) = true
    simp [delay, unqueued]
  · change (decide (1 ≤ f.integers 0) && true) = true
    simp [delay]

set_option maxRecDepth 16384 in
private theorem unaffectedEmpty :
    ∀ inv ∈ (earlier ++ middle) ++ later,
      obligationsFor rule_5 none [inv] = atTarget 0 [inv] := by
  apply List.map_inj_left.mp
  rfl

set_option maxRecDepth 16384 in
private theorem unaffectedPending :
    ∀ inv ∈ (earlier ++ middle) ++ later,
      obligationsFor rule_10 none [inv] = atTarget 0 [inv] := by
  apply List.map_inj_left.mp
  rfl

private theorem applyUnchanged (rule : Rule) (s : Snapshot) (f : Values)
    (valid : invariantsHold model s = true) (state : s.state = 0)
    (equal : ∀ inv ∈ (earlier ++ middle) ++ later,
      obligationsFor rule none [inv] = atTarget 0 [inv]) :
    ∀ inv ∈ (earlier ++ middle) ++ later, inv ∈ model.invariants →
      holds (obligationsFor rule none [inv]) s f = true := by
  intro inv found member
  rw [equal inv found, ← state, holds_atCurrent]
  simpa [holds] using List.all_eq_true.mp valid inv member

theorem config_empty : Approved.raw_5_external := by
  apply preserves_clauses
  intro s f valid source enabled
  change (TypedMachine.eval s f e16 && TypedMachine.eval s f e50) = true at enabled
  simp only [Bool.and_eq_true] at enabled
  have phase := implyEnabled s e16 e1593
    (List.all_eq_true.mp valid e1594 (by rw [model_invariants]; simp)) enabled.1
  have state : TypedMachine.eval s zeroValues e15 = TypedMachine.eval s zeroValues e6 :=
    of_decide_eq_true enabled.1
  have pending : TypedMachine.eval s zeroValues e35 = false := by
    change decide (TypedMachine.eval s zeroValues e15 = TypedMachine.eval s zeroValues e34) = false
    rw [state]
    rfl
  have unqueued := no_queue s valid pending
  refine ⟨rfl, config_clauses _ s f (applyUnchanged _ s f valid source unaffectedEmpty) ?_⟩
  refine ⟨?_, rfl, rfl, ?_, ?_, rfl, trivial⟩
  · change (TypedMachine.eval s f e1593 && true) = true
    simp [show TypedMachine.eval s f e1593 = true from phase]
  · change (TypedMachine.eval s f e50 && true) = true
    simp [enabled.2]
  · change (((!TypedMachine.eval s f e1613) || false) && true) = true
    simp [show TypedMachine.eval s f e1613 = false from unqueued]

theorem config_pending : Approved.raw_10_external := by
  apply preserves_clauses
  intro s f valid source enabled
  change (TypedMachine.eval s f e35 && TypedMachine.eval s f e50) = true at enabled
  simp only [Bool.and_eq_true] at enabled
  have phase := implyEnabled s e35 e1596
    (List.all_eq_true.mp valid e1597 (by rw [model_invariants]; simp)) enabled.1
  refine ⟨rfl, config_clauses _ s f (applyUnchanged _ s f valid source unaffectedPending) ?_⟩
  refine ⟨rfl, ?_, rfl, ?_, ?_, rfl, trivial⟩
  · change (TypedMachine.eval s f e1596 && true) = true
    simp [show TypedMachine.eval s f e1596 = true from phase]
  · change (TypedMachine.eval s f e50 && true) = true
    simp [enabled.2]
  · change (((!TypedMachine.eval s f e1613) || true) && true) = true
    simp

def firings : List (Rule × Option Nat) := [(rule_5, none), (rule_10, none), (rule_13, none)]

theorem checked : Each (fun p => FiringPreserves model p.1 p.2) firings :=
  ⟨config_empty, config_pending, config_resolved, trivial⟩

private theorem configMember (index : Nat) (rule : Rule)
    (selected : model.rules[index]? = some rule) (external : rule.event ∈ model.externalEvents) :
    (rule, none) ∈ rawChecks model declaredTimers :=
  raw_external_member model declaredTimers rule (List.mem_iff_getElem?.mpr ⟨index, selected⟩) external

theorem members : Each (fun p => p ∈ rawChecks model declaredTimers) firings :=
  ⟨configMember 5 rule_5 rfl (by decide), configMember 10 rule_10 rfl (by decide),
    configMember 13 rule_13 rfl (by decide), trivial⟩

#print axioms config_empty
#print axioms config_pending
#print axioms config_resolved
end TCPIPCacheConfig
