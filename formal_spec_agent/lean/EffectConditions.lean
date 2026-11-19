import ExprRewrite
import TypedFiringContracts
import TimerInvariantFacts
import EffectFootprint

namespace FormalSpecAgent.EffectConditions
open TypedIR TypedMachine TypedContracts TypedFiringContracts TimerInvariantFacts ExprRewrite

private def identity : Rewrite :=
  ⟨Expr.variable, Expr.field, Expr.stateIs, Expr.timerActive⟩

private def kindEq (a b : Kind) : Decidable (a = b) := by
  cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)

local instance (k l : Kind) : Decidable (k = l) := kindEq k l

private def assign (kind : Kind) (slot : Nat) (value : Expr kind) : Rewrite :=
  { identity with varRead := fun k n =>
      if same : k = kind then
        if n = slot then same.symm ▸ value else .variable k n
      else .variable k n }

private def timer (owner : Nat) (active : Bool) : Rewrite :=
  { identity with timerActive := fun n =>
      if n = owner then .literal .boolean active else .timerActive n }

private def target (state : Nat) : Rewrite :=
  { identity with field := fun k n => .literal k (getValue k zeroValues n)
                  stateIs := fun id => .literal .boolean (decide (state = id)) }

def holds (checks : List (Expr .boolean)) (s : Snapshot) (f : Values) : Bool :=
  checks.all (TypedMachine.eval s f)

private theorem holds_rewrite (mapping : Rewrite) (s t : Snapshot) (f g : Values)
    (interprets : Interprets mapping (context s f) (context t g)) (checks : List (Expr .boolean)) :
    holds (checks.map (run mapping)) s f = holds checks t g := by
  induction checks with
  | nil => rfl
  | cons x rest ih =>
    simp only [holds, List.map_cons, List.all_cons] at *
    have head : TypedMachine.eval s f (run mapping x) = TypedMachine.eval t g x :=
      sound mapping _ _ interprets x
    rw [head, ih]

private theorem assign_sound (k : Kind) (slot : Nat) (value : Expr k) (s : Snapshot) (f : Values) :
    Interprets (assign k slot value) (context s f)
      (context {s with values := setValue k slot (TypedMachine.eval s f value) s.values} f) := by
  constructor
  · intro l n
    cases l <;> cases k <;> simp [assign, identity, context, TypedIR.eval, getValue, setValue,
      TypedMachine.eval]
    all_goals
      split <;> rfl
  · intro k n; rfl
  · intro id; rfl
  · intro id; rfl

private theorem cancel_sound (s : Snapshot) (f : Values) (owner : Nat) :
    Interprets (timer owner false) (context s f) (context (cancelTimer s owner) f) := by
  constructor
  · intro k n; rfl
  · intro k n; rfl
  · intro id; rfl
  · intro id
    by_cases same : id = owner <;>
      simp [timer, same, identity, TypedIR.eval, context, cancelActive]

private theorem arm_sound (s next : Snapshot) (f : Values) (owner : Nat) (delay : Int)
    (armed : armTimer s owner delay = .ok next) :
    Interprets (timer owner true) (context s f) (context next f) := by
  have keepTimers (id) := armActive s next owner id delay armed
  have unchanged : next.values = s.values ∧ next.state = s.state := by
    unfold armTimer at armed
    split at armed
    · contradiction
    · rw [← Except.ok.inj armed]
      exact ⟨rfl, rfl⟩
  constructor
  · intro k n; simp [timer, identity, context, TypedIR.eval, unchanged.1]
  · intro k n; rfl
  · intro id; simp [timer, identity, context, TypedIR.eval, unchanged.2]
  · intro id
    by_cases same : id = owner <;>
      simp [timer, same, identity, TypedIR.eval, context, keepTimers]

/-- Substitutes each action back into the obligations for the following steps.
An arm adds its own positive-delay check before activity is substituted. -/
def beforeActions : List Action → List (Expr .boolean) → List (Expr .boolean)
  | [], checks => checks
  | .assign kind slot expr :: rest, checks =>
      (beforeActions rest checks).map (run (assign kind slot expr))
  | .cancel owner :: rest, checks => (beforeActions rest checks).map (run (timer owner false))
  | .arm owner delay :: rest, checks =>
      .intGe delay (.literal .integer 1) :: (beforeActions rest checks).map (run (timer owner true))
  | .emit .. :: rest, checks => beforeActions rest checks

theorem beforeActions_sound (actions : List Action) (checks : List (Expr .boolean))
    (s : Snapshot) (f : Values) (out : List Message) (valid : holds (beforeActions actions checks) s f = true) :
    ∃ after emitted, work actions s f out = .ok (after, emitted) ∧ holds checks after f = true := by
  induction actions generalizing s out with
  | nil => exact ⟨s, out, rfl, valid⟩
  | cons action rest ih =>
    cases action with
    | «assign» kind slot value =>
      simp only [beforeActions, holds_rewrite _ _ _ _ _ (assign_sound kind slot value s f)] at valid
      exact ih _ _ valid
    | cancel owner =>
      simp only [beforeActions, holds_rewrite _ _ _ _ _ (cancel_sound s f owner)] at valid
      exact ih _ _ valid
    | emit msg fields => exact ih _ _ valid
    | arm owner delay =>
      simp only [beforeActions, holds, List.all_cons, Bool.and_eq_true] at valid
      have enough : 1 ≤ TypedMachine.eval s f delay := of_decide_eq_true valid.1
      let next := { s with timers := (cancelTimer s owner).timers ++
        [TimerEntry.mk owner (s.now + TypedMachine.eval s f delay)] }
      have armed : armTimer s owner (TypedMachine.eval s f delay) = .ok next := by
        have positive : ¬ TypedMachine.eval s f delay ≤ 0 :=
          Int.not_le.mpr (Int.lt_of_lt_of_le (by decide : (0 : Int) < 1) enough)
        simp [armTimer, next, cancelTimer, positive]
      have sufficient := valid.2
      change holds ((beforeActions rest checks).map (run (timer owner true))) s f = true at sufficient
      rw [holds_rewrite _ _ _ _ _ (arm_sound s next f owner _ armed)] at sufficient
      obtain ⟨after, emitted, result, post⟩ := ih next out sufficient
      exact ⟨after, emitted, by simp only [work, armed, result], post⟩

private theorem target_sound (s : Snapshot) (f : Values) (targetState : Nat) :
    Interprets (target targetState) (context s f) (context {s with state := targetState} zeroValues) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- Observe the invariants at the rule target with zero event fields,
as the original invariant evaluator does. -/
def atTarget (state : Nat) (checks : List (Expr .boolean)) : List (Expr .boolean) :=
  checks.map (run (target state))

theorem holds_atTarget (state : Nat) (checks : List (Expr .boolean)) (s : Snapshot) (f : Values) :
    holds (atTarget state checks) s f = holds checks {s with state := state} zeroValues :=
  holds_rewrite _ _ _ _ _ (target_sound s f state) checks

theorem holds_atCurrent (checks : List (Expr .boolean)) (s : Snapshot) (f : Values) :
    holds (atTarget s.state checks) s f = holds checks s zeroValues := by
  rw [holds_atTarget]

/-- Derive scoped obligations from the exact original rule and firing. -/
def obligationsFor (rule : Rule) (firing : Option Nat)
    (invariants : List (Expr .boolean)) : List (Expr .boolean) :=
  let before := beforeActions rule.actions (atTarget rule.target invariants)
  match firing with
  | none => before
  | some owner => before.map (run (timer owner false))

def obligations (model : Model) (rule : Rule) (firing : Option Nat) : List (Expr .boolean) :=
  obligationsFor rule firing model.invariants

private theorem interpret (model : Model) (rule : Rule) (firing : Option Nat)
    (invariants : List (Expr .boolean)) (s : Snapshot) (f : Values)
    (ok : holds (obligationsFor rule firing invariants) s f = true) :
    ∃ t, candidate s rule f rule.event firing = .ok t ∧
      invariantsHold {model with invariants := invariants} t.after = true := by
  have pre : holds (beforeActions rule.actions (atTarget rule.target invariants))
      (withoutFiring s firing) f = true := by
    cases firing with
    | none => exact ok
    | some owner =>
      unfold obligationsFor at ok
      rw [holds_rewrite _ _ _ _ _ (cancel_sound s f owner)] at ok
      exact ok
  obtain ⟨after, sent, ran, holdsAfter⟩ := beforeActions_sound rule.actions _ _ f [] pre
  rw [holds_atTarget] at holdsAfter
  let t : Transition := ⟨{after with state := rule.target}, rule.id, rule.event, f, sent⟩
  exact ⟨t, by simp only [candidate, ran, t], holdsAfter⟩

theorem preserves (model : Model) (rule : Rule) (firing : Option Nat)
    (checked : ∀ s f, invariantsHold model s = true → s.state = rule.source →
      TypedMachine.eval s f rule.guard = true → holds (obligations model rule firing) s f = true) :
    FiringPreserves model rule firing :=
  fun s f valid source enabled => interpret model rule firing model.invariants s f
    (checked s f valid source enabled)

/-- Prove totality and then certify each original invariant independently.
All witnesses describe the same deterministic evaluation of the original rule. -/
theorem preserves_clauses (model : Model) (rule : Rule) (firing : Option Nat)
    (checked : ∀ s f, invariantsHold model s = true → s.state = rule.source →
      TypedMachine.eval s f rule.guard = true →
      holds (obligationsFor rule firing []) s f = true ∧
      ∀ clause ∈ model.invariants, holds (obligationsFor rule firing [clause]) s f = true) :
    FiringPreserves model rule firing := by
  intro s f valid source enabled
  obtain ⟨total, clauses⟩ := checked s f valid source enabled
  obtain ⟨t, ran, _⟩ := interpret model rule firing [] s f total
  refine ⟨t, ran, List.all_eq_true.mpr ?_⟩
  intro clause member
  obtain ⟨witness, ranAgain, post⟩ := interpret model rule firing [clause] s f (clauses clause member)
  rw [ran] at ranAgain
  cases Except.ok.inj ranAgain
  simpa [invariantsHold] using post

/-- Reuse the input evidence for clauses unaffected by the firing. -/
theorem preserves_touched (model : Model) (rule : Rule) (firing : Option Nat)
    (checked : ∀ s f, invariantsHold model s = true → s.state = rule.source →
      TypedMachine.eval s f rule.guard = true →
      holds (obligationsFor rule firing []) s f = true ∧
      ∀ clause ∈ model.invariants, EffectFootprint.ignoresFiring clause rule firing = false →
        holds (obligationsFor rule firing [clause]) s f = true) :
    FiringPreserves model rule firing := by
  intro s f valid source enabled
  obtain ⟨total, clauses⟩ := checked s f valid source enabled
  obtain ⟨t, ran, _⟩ := interpret model rule firing [] s f total
  refine ⟨t, ran, List.all_eq_true.mpr ?_⟩
  intro clause member
  cases footprint : EffectFootprint.ignoresFiring clause rule firing with
  | true =>
    exact (EffectFootprint.candidate_same_eval clause rule firing s f zeroValues t source footprint ran).trans
      (List.all_eq_true.mp valid clause member)
  | false =>
    obtain ⟨witness, ranAgain, post⟩ :=
      interpret model rule firing [clause] s f (clauses clause member footprint)
    rw [ran] at ranAgain
    cases Except.ok.inj ranAgain
    simpa [invariantsHold] using post

end FormalSpecAgent.EffectConditions
