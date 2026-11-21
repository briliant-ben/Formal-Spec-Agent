import EffectFootprint

namespace FormalSpecAgent.GuardedSuffix
open TypedIR TypedMachine TypedContracts TypedFiringContracts InvariantFootprint EffectFootprint

private theorem work_append (initial trailing : List Action) (s : Snapshot) (f : Values)
    (out : List Message) :
    work (initial ++ trailing) s f out =
      (work initial s f out).bind (fun (after, sent) => work trailing after f sent) := by
  induction initial generalizing s out with
  | nil => rfl
  | cons action rest ih =>
    cases action with
    | «assign» k slot value => exact ih _ _
    | emit name fields => exact ih _ _
    | cancel owner => exact ih _ _
    | arm owner delay =>
      simp only [List.cons_append, work]
      cases armTimer s owner (TypedMachine.eval s f delay) with
      | error fault => rfl
      | ok after => exact ih after out

/-- A final literal write confirmed by the original guard can be erased when
preceding actions leave that slot intact. The original candidate is unchanged. -/
theorem preserves_after_removing_text (model : Model) (rule : Rule) (firing : Option Nat)
    (initial : List Action) (slot : Nat) (value : String)
    (actions : rule.actions = initial ++ [.assign .text slot (.literal .text value)])
    (untouched : initial.all (ignoresAction (.variable .text slot)) = true)
    (guardValue : ∀ s f, TypedMachine.eval s f rule.guard = true → getValue .text s.values slot = value)
    (shorter : FiringPreserves model {rule with actions := initial} firing) :
    FiringPreserves model rule firing := by
  intro s f valid source enabled
  obtain ⟨transition, executed, afterValid⟩ := shorter s f valid source enabled
  refine ⟨transition, ?_, afterValid⟩
  unfold candidate at executed ⊢
  rw [actions, work_append]
  cases ran : work initial (withoutFiring s firing) f [] with
  | error fault => simp [ran] at executed
  | ok outcome =>
    rcases outcome with ⟨after, sent⟩
    have same := (work_same_eval (.variable .text slot) initial _ after f f [] sent untouched ran).2
    have original : (withoutFiring s firing).values = s.values := by cases firing <;> rfl
    change getValue .text after.values slot = getValue .text (withoutFiring s firing).values slot at same
    rw [original, guardValue s f enabled] at same
    have write : setValue .text slot value after.values = after.values := by
      rw [← same]
      exact set_current_value .text slot after.values
    simpa only [Except.bind, work, TypedMachine.eval, TypedIR.eval, write, ran] using executed

end FormalSpecAgent.GuardedSuffix
