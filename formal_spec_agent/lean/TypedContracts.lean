import TypedMachine

namespace FormalSpecAgent.TypedContracts

open FormalSpecAgent.TypedMachine
open FormalSpecAgent.TypedIR

/-- Raw candidate transition: perform actions with firing removed (if any), then set target state.
No invariant filtering. -/
def candidate (snapshot : Snapshot) (rule : Rule) (fields : Values) (event : Nat)
    (firing : Option Nat) : Except Fault Transition :=
  match work rule.actions (withoutFiring snapshot firing) fields [] with
  | .error f => .error f
  | .ok (snap, emitted) =>
    .ok { after := { snap with state := rule.target }, rule := rule.id, event := event,
          fields := fields, emitted := emitted }

/-- RulePreserves: for every snapshot and typed fields, if invariants hold initially,
state is rule.source, and guard evaluates true, then candidate succeeds and final invariants hold.
Existential ensures total successful effects, not vacuous if all candidates error. -/
def RulePreserves (model : Model) (rule : Rule) : Prop :=
  ∀ (snapshot : Snapshot) (fields : Values),
    invariantsHold model snapshot = true →
    snapshot.state = rule.source →
    eval snapshot fields rule.guard = true →
    ∃ t : Transition,
      candidate snapshot rule fields rule.event none = .ok t ∧
      invariantsHold model t.after = true

/-- InitialValid: invariants hold in initial snapshot. -/
def InitialValid (model : Model) (initial : Snapshot) : Prop :=
  invariantsHold model initial = true

/-- GuardsDisjoint: for any two distinct rules in model that match the same state and event,
their guards cannot both be true on any snapshot/fields satisfying invariants. -/
def GuardsDisjoint (model : Model) : Prop :=
  ∀ (snapshot : Snapshot) (fields : Values),
    invariantsHold model snapshot = true →
    ∀ (event : Nat) (r1 r2 : Rule),
      r1 ∈ model.rules → r2 ∈ model.rules →
      r1.id ≠ r2.id →
      r1.source = snapshot.state → r2.source = snapshot.state →
      r1.event = event → r2.event = event →
      eval snapshot fields r1.guard = false ∨ eval snapshot fields r2.guard = false

/-- Covers: for any snapshot whose state is in declared states, any external event and arbitrary
fields, if initial invariants hold then there is a member rule with matching source/event and true guard. -/
def Covers (model : Model) (states : List Nat) : Prop :=
  ∀ (snapshot : Snapshot) (event : Nat) (fields : Values),
    snapshot.state ∈ states →
    event ∈ model.externalEvents →
    invariantsHold model snapshot = true →
    ∃ r : Rule,
      r ∈ model.rules ∧
      r.source = snapshot.state ∧
      r.event = event ∧
      eval snapshot fields r.guard = true

/-- Enables: witness proposition for a rule/snapshot/fields/expected transition.
Assumes initial invariant, source state, guard true, exact candidate = expected, and final invariant. -/
def Enables (model : Model) (rule : Rule) (snapshot : Snapshot) (fields : Values)
    (expected : Transition) : Prop :=
  invariantsHold model snapshot = true ∧
  snapshot.state = rule.source ∧
  eval snapshot fields rule.guard = true ∧
  candidate snapshot rule fields rule.event none = .ok expected ∧
  invariantsHold model expected.after = true

/-- runRule_eq_filter: actual runRule (which applies invariants filter) equals raw candidate
filtered by seeing if candidate result is ok and then checking invariants on after.
More precisely: if candidate errors, runRule returns same error; if candidate ok,
runRule returns ok if invariantsHold after else error invariant. -/
theorem runRule_eq_filter (model : Model) (snapshot : Snapshot) (rule : Rule)
    (fields : Values) (event : Nat) (firing : Option Nat) :
    runRule model snapshot rule fields event firing =
      match candidate snapshot rule fields event firing with
      | .error f => .error f
      | .ok t => if invariantsHold model t.after then .ok t else .error .invariant :=
by
  unfold runRule candidate
  cases h : work rule.actions (withoutFiring snapshot firing) fields [] with
  | error fault => rfl
  | ok pair =>
    rcases pair with ⟨snapshot, emitted⟩
    rfl

/-- preserving_rule_succeeds: RulePreserves plus actual initial invariant/source/guard facts
implies exists t, actual runRule returns ok t and invariantsHold t.after = true.
Derived from raw preservation and runRule_eq_filter. -/
theorem preserving_rule_succeeds (model : Model) (rule : Rule) (snapshot : Snapshot)
    (fields : Values) :
    RulePreserves model rule →
    invariantsHold model snapshot = true →
    snapshot.state = rule.source →
    eval snapshot fields rule.guard = true →
    ∃ t : Transition,
      runRule model snapshot rule fields rule.event none = .ok t ∧
      invariantsHold model t.after = true :=
by
  intro hPres hInv hSrc hGuard
  have hRaw : ∃ t : Transition,
      candidate snapshot rule fields rule.event none = .ok t ∧
      invariantsHold model t.after = true :=
    hPres snapshot fields hInv hSrc hGuard
  rcases hRaw with ⟨t, hcand, hAfter⟩
  have hrun : runRule model snapshot rule fields rule.event none = .ok t :=
    by
      rw [runRule_eq_filter]
      rw [hcand]
      simp [hAfter]
  exact ⟨t, hrun, hAfter⟩

end FormalSpecAgent.TypedContracts
