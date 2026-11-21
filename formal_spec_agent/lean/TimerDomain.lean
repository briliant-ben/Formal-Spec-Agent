import TypedMachine

namespace FormalSpecAgent.TimerDomain

open TypedMachine

def Declared (ids : List Nat) (s : Snapshot) : Prop :=
  ∀ entry ∈ s.timers, entry.timer ∈ ids

def ArmsDeclared (ids : List Nat) (model : Model) : Prop :=
  ∀ rule ∈ model.rules, ∀ timer delay, Action.arm timer delay ∈ rule.actions → timer ∈ ids

theorem cancel_declared (ids : List Nat) (s : Snapshot) (timer : Nat)
    (valid : Declared ids s) : Declared ids (cancelTimer s timer) :=
  fun entry member => valid entry (List.mem_filter.mp member).1

theorem work_declared (ids : List Nat) (actions : List Action) (s : Snapshot)
    (fields : TypedIR.Values) (out : List Message) (after : Snapshot) (emitted : List Message)
    (valid : Declared ids s)
    (arms : ∀ timer delay, Action.arm timer delay ∈ actions → timer ∈ ids)
    (executed : work actions s fields out = .ok (after, emitted)) :
    Declared ids after := by
  induction actions generalizing s out with
  | nil =>
    simp [work] at executed
    exact executed.1 ▸ valid
  | cons action rest ih =>
    have tailArms : ∀ timer delay, Action.arm timer delay ∈ rest → timer ∈ ids :=
      fun timer delay member => arms timer delay (List.mem_cons_of_mem _ member)
    cases action with
    | assign kind slot expression =>
      exact ih {s with values := setValue kind slot (eval s fields expression) s.values}
        out valid tailArms executed
    | emit name expressions => exact ih _ _ valid tailArms executed
    | cancel timer => exact ih _ _ (cancel_declared ids s timer valid) tailArms executed
    | arm timer delay =>
      simp only [work] at executed
      cases armed : armTimer s timer (eval s fields delay) with
      | error fault => simp [armed] at executed
      | ok next =>
        simp only [armed] at executed
        have declared : timer ∈ ids := arms timer delay (List.mem_cons_self ..)
        unfold armTimer at armed
        split at armed
        · contradiction
        · injection armed with equal
          subst next
          apply ih _ _ _ tailArms executed
          intro entry member
          rcases List.mem_append.mp member with old | fresh
          · exact valid entry (List.mem_filter.mp old).1
          · cases List.mem_singleton.mp fresh
            exact declared

theorem fire_declared (ids : List Nat) (model : Model) (s : Snapshot) (event : Nat)
    (fields : TypedIR.Values) (firing : Option Nat) (transition : Transition)
    (valid : Declared ids s) (arms : ArmsDeclared ids model)
    (executed : fire model s event fields firing = .ok transition) :
    Declared ids transition.after := by
  have inputValid : Declared ids (withoutFiring s firing) := by
    cases firing with
    | none => exact valid
    | some timer => exact cancel_declared ids s timer valid
  unfold fire at executed
  split at executed
  · contradiction
  · rename_i rule selected
    have member : rule ∈ enabled model s event fields := by simp [selected]
    have fromModel := (List.mem_filter.mp member).1
    unfold runRule at executed
    split at executed
    · contradiction
    · rename_i after emitted worked
      dsimp only at executed
      split at executed
      · injection executed with equal
        subst transition
        exact work_declared ids _ _ fields [] after emitted inputValid (arms rule fromModel) worked
      · contradiction
  · contradiction

theorem external_declared (ids : List Nat) (model : Model) (s : Snapshot) (event : Nat)
    (fields : TypedIR.Values) (time : Int) (transition : Transition)
    (valid : Declared ids s) (arms : ArmsDeclared ids model)
    (executed : external model s event fields time = .ok transition) :
    Declared ids transition.after := by
  unfold external at executed
  split at executed
  · contradiction
  · split at executed
    · contradiction
    · split at executed
      · split at executed
        · contradiction
        · exact fire_declared ids model {s with now := time} event fields none transition valid arms executed
      · exact fire_declared ids model {s with now := time} event fields none transition valid arms (by simpa using executed)

theorem step_declared (ids : List Nat) (model : Model) (s : Snapshot) (time : Int)
    (transition : Transition) (valid : Declared ids s) (arms : ArmsDeclared ids model)
    (executed : stepTimer model s time = .ok transition) :
    Declared ids transition.after := by
  unfold stepTimer at executed
  split at executed
  · contradiction
  · split at executed
    · contradiction
    · rename_i entry _
      split at executed
      · contradiction
      · exact fire_declared ids model {s with now := time} _ zeroValues (some entry.timer) transition valid arms executed

end FormalSpecAgent.TimerDomain
