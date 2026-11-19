import BatchReplay
import ScheduledPreservation
import TimerDomain

namespace FormalSpecAgent.BatchPreservation

open TypedMachine TimerRank BatchMachine BatchReplay ScheduledPreservation TimerDomain

/-- The model supplies a raw obligation for each declared timer and its IR event. -/
def TimerRaw (ids : List Nat) (model : Model) : Prop :=
  ∀ timer ∈ ids, MatchingRaw model (model.timerEvents timer) (some timer)

def Preserved (ids : List Nat) (model : Model) (batch : Batch) : Prop :=
  invariantsHold model batch.after = true ∧ Declared ids batch.after ∧
    ∀ transition ∈ batch.trace,
      invariantsHold model transition.after = true ∧ Declared ids transition.after

/-- Induction follows the rank of the actual scheduler, without a bound on the
    number of firings. The proof uses the raw obligation at every step. -/
theorem advance_from_raw (ids : List Nat) (model : Model) (limit : Int)
    (arms : ArmsDeclared ids model) (raw : TimerRaw ids model)
    (s : Snapshot) (timed : WellTimed s) (bound : s.now ≤ limit)
    (valid : invariantsHold model s = true) (declared : Declared ids s) (batch : Batch)
    (executed : advance model s limit = .ok batch) :
    Preserved ids model batch := by
  rw [advance_equation model s limit timed bound] at executed
  cases selected : nextTimer s with
  | none =>
    simp only [selected, Except.ok.injEq] at executed
    subst batch
    exact ⟨(TypedFiringContracts.invariants_clock_irrelevant model s limit).symm.trans valid, declared,
      by simp⟩
  | some entry =>
    simp only [selected] at executed
    by_cases due : entry.due ≤ limit
    · simp only [ite_eq_left due] at executed
      cases fired : stepTimer model s entry.due with
      | error fault => simp [fired] at executed
      | ok transition =>
        simp only [fired] at executed
        have nextValid := timer_success_invariant_from_raw model s entry.due transition
          (fun timer member => raw timer.timer (declared timer member)) valid fired
        have nextDeclared := step_declared ids model s entry.due transition declared arms fired
        have progress := TimerProgress.step_progress model s limit entry transition
          timed bound selected due fired
        have nextBound : transition.after.now ≤ limit := progress.2.1 ▸ due
        cases continued : advance model transition.after limit with
        | error fault => simp [continued, prepend] at executed
        | ok tail =>
          simp [continued, prepend] at executed
          subst batch
          obtain ⟨finalValid, finalDeclared, traceValid⟩ :=
            advance_from_raw ids model limit arms raw transition.after progress.1 nextBound
              nextValid nextDeclared tail continued
          refine ⟨finalValid, finalDeclared, ?_⟩
          intro item member
          rcases List.mem_cons.mp member with head | rest
          · exact head ▸ ⟨nextValid, nextDeclared⟩
          · exact traceValid item rest
    · simp only [ite_eq_right due, Except.ok.injEq] at executed
      subst batch
      exact ⟨(TypedFiringContracts.invariants_clock_irrelevant model s limit).symm.trans valid, declared,
        by simp⟩
termination_by rank limit s
decreasing_by exact progress.2.2

theorem tick_from_raw (ids : List Nat) (model : Model) (limit : Int)
    (arms : ArmsDeclared ids model) (raw : TimerRaw ids model)
    (s : Snapshot) (timed : WellTimed s) (bound : s.now ≤ limit)
    (valid : invariantsHold model s = true) (declared : Declared ids s) (batch : Batch)
    (executed : tick model s limit = .ok batch) :
    Preserved ids model batch := by
  unfold tick at executed
  cases advanced : advance model s limit with
  | error fault => simp [advanced] at executed
  | ok result =>
    have preserved := advance_from_raw ids model limit arms raw s timed bound valid declared result advanced
    simp [advanced, preserved.1] at executed
    subst batch
    exact preserved

theorem dispatch_from_raw (ids : List Nat) (model : Model) (event : Nat) (fields : TypedIR.Values)
    (limit : Int) (arms : ArmsDeclared ids model) (timersRaw : TimerRaw ids model)
    (externalRaw : event ∈ model.externalEvents → MatchingRaw model event none)
    (s : Snapshot) (timed : WellTimed s) (bound : s.now ≤ limit)
    (valid : invariantsHold model s = true) (declared : Declared ids s) (batch : Batch)
    (executed : dispatch model s event fields limit = .ok batch) :
    Preserved ids model batch := by
  unfold dispatch at executed
  split at executed
  · contradiction
  · rename_i allowed
    have member : event ∈ model.externalEvents := by simpa using allowed
    cases advanced : advance model s limit with
    | error fault => simp [advanced] at executed
    | ok prefixBatch =>
      have preserved := advance_from_raw ids model limit arms timersRaw s timed bound valid declared prefixBatch advanced
      simp only [advanced] at executed
      cases dispatched : external model prefixBatch.after event fields prefixBatch.after.now with
      | error fault => simp [dispatched] at executed
      | ok transition =>
        have finalValid := external_success_invariant_from_raw model prefixBatch.after event fields
          prefixBatch.after.now transition externalRaw preserved.1 dispatched
        have finalDeclared := external_declared ids model prefixBatch.after event fields
          prefixBatch.after.now transition preserved.2.1 arms dispatched
        simp [dispatched] at executed
        subst batch
        refine ⟨finalValid, finalDeclared, ?_⟩
        intro item inside
        rcases List.mem_append.mp inside with prefixMember | lastMember
        · exact preserved.2.2 item prefixMember
        · exact (List.mem_singleton.mp lastMember).symm ▸ ⟨finalValid, finalDeclared⟩

end FormalSpecAgent.BatchPreservation
