import InvariantFootprint
import TimerInvariantFacts

namespace FormalSpecAgent.EffectFootprint
open TypedMachine TypedIR TypedContracts InvariantFootprint TimerInvariantFacts

private theorem eval_timer_change {kind : Kind} (expr : Expr kind) (ctx : Context)
    (owner : Nat) (timers : List Nat)
    (equal : ∀ id, id ≠ owner → (id ∈ timers ↔ id ∈ ctx.activeTimers))
    (unobserved : ignoresTimer owner expr = true) :
    TypedIR.eval expr {ctx with activeTimers := timers} = TypedIR.eval expr ctx := by
  induction expr with
  | timerActive id =>
    have distinct : id ≠ owner := by
      simp only [ignoresTimer, admitsReads, bne_iff_ne] at unobserved
      exact Ne.symm unobserved
    simp only [TypedIR.eval, equal id distinct]
  | _ => simp_all [TypedIR.eval, ignoresTimer, admitsReads, Bool.and_eq_true]

private theorem eval_cancel {kind : Kind} (expr : Expr kind) (s : Snapshot) (f : Values)
    (owner : Nat) (unobserved : ignoresTimer owner expr = true) :
    TypedMachine.eval (cancelTimer s owner) f expr = TypedMachine.eval s f expr := by
  apply eval_timer_change expr (context s f) owner _ _ unobserved
  intro id distinct
  simp [context, cancelActive, distinct]

private theorem eval_arm {kind : Kind} (expr : Expr kind) (s after : Snapshot) (f : Values)
    (owner : Nat) (delay : Int) (armed : armTimer s owner delay = .ok after)
    (unobserved : ignoresTimer owner expr = true) :
    TypedMachine.eval after f expr = TypedMachine.eval s f expr := by
  have same (id : Nat) (distinct : id ≠ owner) :
      id ∈ after.timers.map TimerEntry.timer ↔ id ∈ (context s f).activeTimers := by
    simp [context, armActive s after owner id delay armed, distinct]
  have unchanged : context after f =
      {context s f with activeTimers := after.timers.map TimerEntry.timer} := by
    unfold armTimer at armed
    split at armed
    · contradiction
    · rw [← Except.ok.inj armed]
      rfl
  unfold TypedMachine.eval
  rw [unchanged]
  exact eval_timer_change expr _ owner _ same unobserved

def ignoresAction (expr : Expr kind) : Action → Bool
  | .assign _ slot _ => ignoresSlot slot expr
  | .cancel owner | .arm owner _ => ignoresTimer owner expr
  | .emit .. => true

theorem work_same_eval (expr : Expr kind) (actions : List Action)
    (s after : Snapshot) (f g : Values) (before out : List Message)
    (unobserved : actions.all (ignoresAction expr) = true)
    (executed : work actions s f before = .ok (after, out)) :
    after.state = s.state ∧ TypedMachine.eval after g expr = TypedMachine.eval s g expr := by
  induction actions generalizing s before with
  | nil =>
    have output := Except.ok.inj executed
    cases congrArg Prod.fst output
    exact ⟨rfl, rfl⟩
  | cons action rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at unobserved
    cases action with
    | «assign» kind slot exprValue =>
      have result := ih {s with values := setValue kind slot (TypedMachine.eval s f exprValue) s.values}
        before unobserved.2 executed
      exact ⟨result.1, result.2.trans (eval_after_unrelated_set expr (context s g) kind slot
        (TypedMachine.eval s f exprValue) unobserved.1)⟩
    | emit _ _ => exact ih _ _ unobserved.2 executed
    | cancel owner =>
      have result := ih (cancelTimer s owner) before unobserved.2 executed
      exact ⟨result.1, result.2.trans (eval_cancel expr s g owner unobserved.1)⟩
    | arm owner delay =>
      simp only [work] at executed
      cases armed : armTimer s owner (TypedMachine.eval s f delay) with
      | error fault => simp [armed] at executed
      | ok next =>
        simp only [armed] at executed
        have result := ih next before unobserved.2 executed
        have state : next.state = s.state := by
          unfold armTimer at armed
          split at armed
          · contradiction
          · rw [← Except.ok.inj armed]
        exact ⟨result.1.trans state, result.2.trans (eval_arm expr s next g owner _ armed unobserved.1)⟩

/-- Check whether a firing leaves the expression's reads undisturbed.
State changes are conservatively treated as affecting every expression. -/
def ignoresFiring (expr : Expr kind) (rule : Rule) (firing : Option Nat) : Bool :=
  (rule.target == rule.source) &&
    (firing.all (fun owner => ignoresTimer owner expr)) &&
    rule.actions.all (ignoresAction expr)

theorem candidate_same_eval (expr : Expr kind) (rule : Rule) (firing : Option Nat)
    (s : Snapshot) (f g : Values) (transition : Transition)
    (source : s.state = rule.source)
    (unobserved : ignoresFiring expr rule firing = true)
    (executed : candidate s rule f rule.event firing = .ok transition) :
    TypedMachine.eval transition.after g expr = TypedMachine.eval s g expr := by
  simp only [ignoresFiring, Bool.and_eq_true, beq_iff_eq] at unobserved
  have removed : TypedMachine.eval (withoutFiring s firing) g expr = TypedMachine.eval s g expr := by
    cases firing with
    | none => rfl
    | some owner => exact eval_cancel expr s g owner unobserved.1.2
  unfold candidate at executed
  cases ran : work rule.actions (withoutFiring s firing) f [] with
  | error fault => simp [ran] at executed
  | ok outcome =>
    rcases outcome with ⟨after, out⟩
    simp only [ran] at executed
    rw [← Except.ok.inj executed]
    have evaluates := work_same_eval expr rule.actions _ after f g [] out unobserved.2 ran
    have removedState : (withoutFiring s firing).state = s.state := by cases firing <;> rfl
    have target : rule.target = after.state :=
      unobserved.1.1.trans (source.symm.trans (removedState.symm.trans evaluates.1.symm))
    have restored : {after with state := rule.target} = after := by rw [target]
    change TypedMachine.eval {after with state := rule.target} g expr = TypedMachine.eval s g expr
    rw [restored]
    exact evaluates.2.trans removed

end FormalSpecAgent.EffectFootprint
