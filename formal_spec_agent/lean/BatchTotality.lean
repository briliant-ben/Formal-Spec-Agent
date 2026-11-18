import TimedSelection

namespace FormalSpecAgent.BatchTotality

open TypedMachine TypedIR TypedContracts TypedFiringContracts
open TimerRank TimerMinimum TimerDomain BatchMachine BatchReplay BatchPreservation
open ScheduledPreservation TimedSelection

def TargetsDeclared (model : Model) (states : List Nat) : Prop :=
  ∀ rule ∈ model.rules, rule.target ∈ states

structure Admitted (model : Model) (states ids : List Nat) (s : Snapshot) : Prop where
  valid : invariantsHold model s = true
  state : s.state ∈ states
  timers : Declared ids s
  timed : WellTimed s

structure Contracts (model : Model) (states ids : List Nat) : Prop where
  targets : TargetsDeclared model states
  arms : ArmsDeclared ids model
  unique : (model.rules.map Rule.id).Nodup
  disjoint : GuardsDisjoint model
  timerCoverage : CoversTimers model states ids
  timerRaw : TimerRaw ids model
  externalCoverage : Covers model states
  externalRaw : ∀ event ∈ model.externalEvents, MatchingRaw model event none

theorem fire_target (model : Model) (states : List Nat) (s : Snapshot)
    (event : Nat) (fields : Values) (firing : Option Nat) (t : Transition)
    (targets : TargetsDeclared model states)
    (executed : fire model s event fields firing = .ok t) :
    t.after.state ∈ states := by
  unfold fire at executed
  split at executed
  · contradiction
  · rename_i rule selected
    have enabledMember : rule ∈ enabled model s event fields := by simp [selected]
    have member := (List.mem_filter.mp enabledMember).1
    unfold runRule at executed
    split at executed
    · contradiction
    · dsimp only at executed
      split at executed
      · cases executed
        exact targets rule member
      · contradiction
  · contradiction

theorem timer_target (model : Model) (states : List Nat) (s : Snapshot)
    (entry : TimerEntry) (t : Transition)
    (targets : TargetsDeclared model states)
    (next : nextTimer s = some entry) (timed : s.now ≤ entry.due)
    (executed : stepTimer model s entry.due = .ok t) :
    t.after.state ∈ states := by
  have fired : fire model {s with now := entry.due} (model.timerEvents entry.timer)
      zeroValues (some entry.timer) = .ok t := by
    simpa [stepTimer, next, Int.not_lt.mpr timed] using executed
  exact fire_target model states _ _ _ _ t targets fired

/-- A returned timer batch has reached the requested clock, with all remaining
    deadlines strictly later. State and timer IDs stay in their IR domains. -/
structure Drained (model : Model) (states ids : List Nat) (limit : Int)
    (after : Snapshot) : Prop where
  admitted : Admitted model states ids after
  atLimit : after.now = limit
  future : ∀ timer ∈ after.timers, limit < timer.due

private theorem finish (model : Model) (states ids : List Nat) (s : Snapshot)
    (limit : Int) (admitted : Admitted model states ids s)
    (future : ∀ timer ∈ s.timers, limit < timer.due) :
    Drained model states ids limit {s with now := limit} := by
  refine ⟨⟨?_, admitted.state, admitted.timers, ?_⟩, rfl, future⟩
  · exact (invariants_clock_irrelevant model s limit).symm.trans admitted.valid
  · exact (wellTimed_iff _).mpr (fun timer member => Int.le_of_lt (future timer member))

private theorem next_none (s : Snapshot) (next : nextTimer s = none) :
    s.timers = [] := by
  let pick : Option TimerEntry → TimerEntry → Option TimerEntry := fun best entry =>
    match best with
    | none => some entry
    | some b => if entry.due < b.due ∨ (entry.due = b.due ∧ entry.timer < b.timer)
        then some entry else best
  have nonempty (entries : List TimerEntry) (best : TimerEntry) :
      entries.foldl pick (some best) ≠ none := by
    induction entries generalizing best with
    | nil => simp
    | cons head tail ih =>
      change tail.foldl pick (pick (some best) head) ≠ none
      change tail.foldl pick (if head.due < best.due ∨
        (head.due = best.due ∧ head.timer < best.timer) then some head else some best) ≠ none
      split <;> apply ih
  cases entries : s.timers with
  | nil => rfl
  | cons head tail =>
    change s.timers.foldl pick none = none at next
    rw [entries] at next
    exact (nonempty tail head next).elim

/-- The actual scheduler succeeds for every nondecreasing request time under
    the model contracts. Recursion follows the real scheduler rank. -/
theorem advance_total (model : Model) (states ids : List Nat) (limit : Int)
    (contract : Contracts model states ids) (s : Snapshot)
    (admitted : Admitted model states ids s) (bound : s.now ≤ limit) :
    ∃ batch, advance model s limit = .ok batch ∧
      Drained model states ids limit batch.after ∧ Preserved ids model batch := by
  suffices success : ∃ batch, advance model s limit = .ok batch ∧
      Drained model states ids limit batch.after from by
    obtain ⟨batch, executed, drained⟩ := success
    exact ⟨batch, executed, drained, advance_from_raw ids model limit contract.arms
      contract.timerRaw s admitted.timed bound admitted.valid admitted.timers batch executed⟩
  rw [advance_equation model s limit admitted.timed bound]
  cases next : nextTimer s with
  | none =>
    refine ⟨_, rfl, finish model states ids s limit admitted ?_⟩
    intro timer member
    have empty := next_none s next
    simp [empty] at member
  | some entry =>
    have info := next_info s entry next
    by_cases due : entry.due ≤ limit
    · have timed := (wellTimed_iff _).mp admitted.timed entry info.1
      obtain ⟨transition, fired, valid⟩ := timer_enabled_from_contracts model states ids
        s entry contract.unique contract.disjoint contract.timerCoverage contract.timerRaw
        admitted.valid admitted.timers admitted.state next timed
      have progress := TimerProgress.step_progress model s limit entry transition
        admitted.timed bound next due fired
      have nextBound : transition.after.now ≤ limit := progress.2.1 ▸ due
      have nextAdmitted : Admitted model states ids transition.after :=
        ⟨valid, timer_target model states s entry transition contract.targets next timed fired,
          step_declared ids model s entry.due transition admitted.timers contract.arms fired,
          progress.1⟩
      obtain ⟨tail, continued, drained, _⟩ :=
        advance_total model states ids limit contract transition.after nextAdmitted nextBound
      exact ⟨{ after := tail.after, trace := transition :: tail.trace },
        by simp only [ite_eq_left due, fired, continued, prepend], drained⟩
    · exact ⟨{ after := {s with now := limit}, trace := [] },
        by simp only [ite_eq_right due], finish model states ids s limit admitted
        (fun timer member => Int.lt_of_lt_of_le (Int.lt_of_not_ge due) (info.2 timer member))⟩
termination_by rank limit s
decreasing_by exact progress.2.2

theorem tick_total (model : Model) (states ids : List Nat) (limit : Int)
    (contract : Contracts model states ids) (s : Snapshot)
    (admitted : Admitted model states ids s) (bound : s.now ≤ limit) :
    ∃ batch, tick model s limit = .ok batch ∧
      Drained model states ids limit batch.after ∧ Preserved ids model batch := by
  obtain ⟨batch, executed, drained, preserved⟩ :=
    advance_total model states ids limit contract s admitted bound
  exact ⟨batch, by simp [tick, executed, drained.admitted.valid], drained, preserved⟩

theorem dispatch_total (model : Model) (states ids : List Nat) (limit : Int)
    (contract : Contracts model states ids) (s : Snapshot)
    (admitted : Admitted model states ids s) (bound : s.now ≤ limit)
    (event : Nat) (fields : Values) (allowed : event ∈ model.externalEvents) :
    ∃ batch, dispatch model s event fields limit = .ok batch ∧
      Admitted model states ids batch.after ∧ batch.after.now = limit ∧
      Preserved ids model batch := by
  obtain ⟨prefixBatch, advanced, drained, _⟩ :=
    advance_total model states ids limit contract s admitted bound
  let pre := prefixBatch.after
  have noDue : (match nextTimer pre with
      | some entry => decide (entry.due ≤ pre.now)
      | none => false) = false := by
    cases next : nextTimer pre with
    | none => rfl
    | some entry =>
      have future := drained.future entry (next_info pre entry next).1
      have late : ¬ entry.due ≤ pre.now := by
        change ¬ entry.due ≤ prefixBatch.after.now
        rw [drained.atLimit]
        omega
      simpa only [decide_eq_false_iff_not] using late
  obtain ⟨transition, externalDone, valid⟩ := external_enabled_from_contracts
    model states pre event fields pre.now contract.unique contract.disjoint
    contract.externalCoverage (contract.externalRaw event allowed) drained.admitted.valid
    drained.admitted.state allowed (Int.le_refl _) noDue
  have fired : fire model pre event fields none = .ok transition := by
    have unchanged : {pre with now := pre.now} = pre := by cases pre; rfl
    cases next : nextTimer pre with
    | none => simpa [external, allowed, next, unchanged] using externalDone
    | some entry =>
      have late : ¬ entry.due ≤ pre.now := by simpa [next] using noDue
      simpa [external, allowed, next, late, unchanged] using externalDone
  have summary := TimerProgress.fire_summary model pre event fields none transition fired
  have final : Admitted model states ids transition.after :=
    ⟨valid, fire_target model states pre event fields none transition contract.targets fired,
      fire_declared ids model pre event fields none transition drained.admitted.timers contract.arms fired,
      summary.2.1 drained.admitted.timed⟩
  let batch : Batch := {after := transition.after, trace := prefixBatch.trace ++ [transition]}
  have done : dispatch model s event fields limit = .ok batch := by
    simp [dispatch, allowed, advanced, pre, externalDone, batch]
  refine ⟨batch, done, final, summary.1.trans drained.atLimit, ?_⟩
  exact dispatch_from_raw ids model event fields limit contract.arms contract.timerRaw
    (contract.externalRaw event) s admitted.timed bound admitted.valid admitted.timers batch done

end FormalSpecAgent.BatchTotality
