import TimerProgress

namespace FormalSpecAgent.BatchMachine

open FormalSpecAgent.TypedMachine
open FormalSpecAgent.TimerRank

structure Batch where
  after : Snapshot
  trace : List Transition

def advanceAux (model : Model) (snapshot : Snapshot) (limit : Int)
    (hwell : WellTimed snapshot) (hbound : snapshot.now ≤ limit) : Except Fault Batch :=
  match hnext : nextTimer snapshot with
  | none =>
    .ok { after := { snapshot with now := limit }, trace := [] }
  | some entry =>
    if hdue : entry.due ≤ limit then
      match hstep : stepTimer model snapshot entry.due with
      | .error f => .error f
      | .ok transition =>
        let hprogress := TimerProgress.step_progress model snapshot limit entry transition
          hwell hbound hnext hdue hstep
        have newBound : transition.after.now ≤ limit := by
          rw [hprogress.2.1]
          exact hdue
        match advanceAux model transition.after limit hprogress.1 newBound with
        | .error f => .error f
        | .ok rest =>
          .ok { after := rest.after, trace := transition :: rest.trace }
    else
      .ok { after := { snapshot with now := limit }, trace := [] }
termination_by rank limit snapshot
decreasing_by
  exact hprogress.2.2

def advance (model : Model) (snapshot : Snapshot) (limit : Int) : Except Fault Batch :=
  letI : Decidable (WellTimed snapshot) :=
    inferInstanceAs (Decidable (snapshot.timers.all (fun e => decide (snapshot.now ≤ e.due)) = true))
  if hlt : limit < snapshot.now then .error .time
  else
    if hwell : WellTimed snapshot then
      advanceAux model snapshot limit hwell (by omega)
    else
      .error .time

def tick (model : Model) (snapshot : Snapshot) (limit : Int) : Except Fault Batch :=
  match advance model snapshot limit with
  | .error f => .error f
  | .ok batch =>
    if TypedMachine.invariantsHold model batch.after then
      .ok batch
    else
      .error .invariant

def dispatch (model : Model) (snapshot : Snapshot) (event : Nat)
    (fields : TypedIR.Values) (limit : Int) : Except Fault Batch :=
  if !(event ∈ model.externalEvents) then .error .timerInjection
  else
    match advance model snapshot limit with
    | .error f => .error f
    | .ok batch =>
      match TypedMachine.external model batch.after event fields batch.after.now with
      | .error f => .error f
      | .ok transition =>
        .ok { after := transition.after, trace := batch.trace ++ [transition] }

def rollback (initial : Snapshot) (result : Except Fault Batch) : Snapshot :=
  match result with
  | .ok batch => batch.after
  | .error _ => initial

theorem rollback_error (initial : Snapshot) (f : Fault) :
    rollback initial (.error f) = initial :=
  by simp [rollback]

/- Keep public calls opaque during proof-cache substitution; explicit equation
   proofs still unfold them. Runtime definitions and domains are unchanged. -/
attribute [irreducible] advance tick dispatch rollback

end FormalSpecAgent.BatchMachine