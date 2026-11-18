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

structure TimerContracts (model : Model) (states ids : List Nat) : Prop where
  targets : TargetsDeclared model states
  arms : ArmsDeclared ids model
  unique : (model.rules.map Rule.id).Nodup
  disjoint : GuardsDisjoint model
  timerCoverage : CoversTimers model states ids
  timerRaw : TimerRaw ids model

structure Contracts (model : Model) (states ids : List Nat) : Prop where
  targets : TargetsDeclared model states
  arms : ArmsDeclared ids model
  unique : (model.rules.map Rule.id).Nodup
  disjoint : GuardsDisjoint model
  timerCoverage : CoversTimers model states ids
  timerRaw : TimerRaw ids model
  externalCoverage : Covers model states
  externalRaw : ∀ event ∈ model.externalEvents, MatchingRaw model event none

theorem Contracts.timerContracts {model : Model} {states ids : List Nat}
    (contract : Contracts model states ids) : TimerContracts model states ids :=
  ⟨contract.targets, contract.arms, contract.unique, contract.disjoint,
    contract.timerCoverage, contract.timerRaw⟩

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
theorem advance_total_with_timers (model : Model) (states ids : List Nat) (limit : Int)
    (contract : TimerContracts model states ids) (s : Snapshot)
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
        advance_total_with_timers model states ids limit contract transition.after nextAdmitted nextBound
      exact ⟨{ after := tail.after, trace := transition :: tail.trace },
        by simp only [ite_eq_left due, fired, continued, prepend], drained⟩
    · exact ⟨{ after := {s with now := limit}, trace := [] },
        by simp only [ite_eq_right due], finish model states ids s limit admitted
        (fun timer member => Int.lt_of_lt_of_le (Int.lt_of_not_ge due) (info.2 timer member))⟩
termination_by rank limit s
decreasing_by exact progress.2.2

theorem advance_total (model : Model) (states ids : List Nat) (limit : Int)
    (contract : Contracts model states ids) (s : Snapshot)
    (admitted : Admitted model states ids s) (bound : s.now ≤ limit) :
    ∃ batch, advance model s limit = .ok batch ∧
      Drained model states ids limit batch.after ∧ Preserved ids model batch :=
  advance_total_with_timers model states ids limit contract.timerContracts s admitted bound

theorem tick_total (model : Model) (states ids : List Nat) (limit : Int)
    (contract : Contracts model states ids) (s : Snapshot)
    (admitted : Admitted model states ids s) (bound : s.now ≤ limit) :
    ∃ batch, tick model s limit = .ok batch ∧
      Drained model states ids limit batch.after ∧ Preserved ids model batch := by
  obtain ⟨batch, executed, drained, preserved⟩ :=
    advance_total model states ids limit contract s admitted bound
  exact ⟨batch, by simp [tick, executed, drained.admitted.valid], drained, preserved⟩

theorem Drained.external_eq_fire {model : Model} {states ids : List Nat}
    {limit : Int} {s : Snapshot} (drained : Drained model states ids limit s)
    (event : Nat) (fields : Values) (allowed : event ∈ model.externalEvents) :
    external model s event fields s.now = fire model s event fields none := by
  cases next : nextTimer s with
  | none => simp [external, allowed, next]
  | some entry =>
    have future := drained.future entry (next_info s entry next).1
    have late : ¬ entry.due ≤ s.now := by rw [drained.atLimit]; omega
    simp [external, allowed, next, late]

/-- If the timer prefix has succeeded but the external event has no enabled
    rule, the entire command fails and rolls back to the original snapshot. -/
theorem dispatch_uncovered (model : Model) (states ids : List Nat) (limit : Int)
    (s : Snapshot) (prefixBatch : Batch) (event : Nat) (fields : Values)
    (allowed : event ∈ model.externalEvents)
    (advanced : advance model s limit = .ok prefixBatch)
    (drained : Drained model states ids limit prefixBatch.after)
    (uncovered : enabled model prefixBatch.after event fields = []) :
    dispatch model s event fields limit = .error .uncovered ∧
      rollback s (dispatch model s event fields limit) = s := by
  have failed : dispatch model s event fields limit = .error .uncovered := by
    simp [dispatch, allowed, advanced, drained.external_eq_fire event fields allowed,
      fire, uncovered]
  exact ⟨failed, by rw [failed]; exact BatchMachine.rollback_error s .uncovered⟩

/-- Some declared events have no transition in any state. This
    static case can reject without evaluating symbolic event fields. -/
def AbsentExternal (model : Model) (event : Nat) : Prop :=
  event ∈ model.externalEvents ∧ event ∉ model.rules.map Rule.event

theorem enabled_absent (model : Model) (s : Snapshot) (event : Nat) (fields : Values)
    (absent : AbsentExternal model event) :
    enabled model s event fields = [] := by
  cases selected : enabled model s event fields with
  | nil => rfl
  | cons rule rest =>
    have member : rule ∈ enabled model s event fields := by simp [selected]
    have facts := List.mem_filter.mp member
    simp only [Bool.and_eq_true, beq_iff_eq] at facts
    exact (absent.2 (List.mem_map.mpr ⟨rule, facts.1, facts.2.1.2⟩)).elim

theorem dispatch_absent (model : Model) (states ids : List Nat) (limit : Int)
    (contract : TimerContracts model states ids) (s : Snapshot)
    (admitted : Admitted model states ids s) (bound : s.now ≤ limit)
    (event : Nat) (fields : Values) (absent : AbsentExternal model event) :
    dispatch model s event fields limit = .error .uncovered ∧
      rollback s (dispatch model s event fields limit) = s := by
  obtain ⟨prefixBatch, advanced, drained, _⟩ :=
    advance_total_with_timers model states ids limit contract s admitted bound
  exact dispatch_uncovered model states ids limit s prefixBatch event fields absent.1
    advanced drained (enabled_absent model prefixBatch.after event fields absent)

/-- Empty-timer snapshots can reject a structurally absent event without
    assuming the model's universal timer or invariant contracts. -/
theorem dispatch_absent_without_timers (model : Model) (s : Snapshot) (limit : Int)
    (emptyTimers : s.timers = []) (bound : s.now ≤ limit)
    (event : Nat) (fields : Values) (absent : AbsentExternal model event) :
    dispatch model s event fields limit = .error .uncovered ∧
      rollback s (dispatch model s event fields limit) = s := by
  let pre := {s with now := limit}
  have timed : WellTimed s := by simp [WellTimed, emptyTimers]
  have advanced : advance model s limit = .ok {after := pre, trace := []} := by
    rw [advance_equation model s limit timed bound]
    simp [nextTimer, emptyTimers, pre]
  have externalFailed : external model pre event fields pre.now = .error .uncovered := by
    have selected : nextTimer pre = none := by simp [nextTimer, pre, emptyTimers]
    simp [external, absent.1, selected, fire, enabled_absent _ _ _ _ absent]
  have failed : dispatch model s event fields limit = .error .uncovered := by
    simp [dispatch, absent.1, advanced, externalFailed]
  exact ⟨failed, by rw [failed]; exact BatchMachine.rollback_error s .uncovered⟩

theorem dispatch_enabled (model : Model) (states ids : List Nat) (limit : Int)
    (contract : TimerContracts model states ids) (s : Snapshot)
    (admitted : Admitted model states ids s) (bound : s.now ≤ limit)
    (event : Nat) (fields : Values) (allowed : event ∈ model.externalEvents)
    (raw : MatchingRaw model event none) (prefixBatch : Batch)
    (advanced : advance model s limit = .ok prefixBatch)
    (drained : Drained model states ids limit prefixBatch.after)
    (covered : ∃ rule, rule ∈ enabled model prefixBatch.after event fields) :
    ∃ batch, dispatch model s event fields limit = .ok batch ∧
      Admitted model states ids batch.after ∧ batch.after.now = limit ∧
      Preserved ids model batch := by
  let pre := prefixBatch.after
  have witness : ∃ r ∈ model.rules, r.source = pre.state ∧ r.event = event ∧
      TypedMachine.eval pre fields r.guard = true := by
    obtain ⟨rule, member⟩ := covered
    have facts := List.mem_filter.mp member
    simp only [Bool.and_eq_true, beq_iff_eq] at facts
    exact ⟨rule, facts.1, facts.2.1.1, facts.2.1.2, facts.2.2⟩
  obtain ⟨transition, fired, valid⟩ := fire_enabled_from_raw
    model pre event fields none contract.unique contract.disjoint
    drained.admitted.valid raw witness
  have summary := TimerProgress.fire_summary model pre event fields none transition fired
  have final : Admitted model states ids transition.after :=
    ⟨valid, fire_target model states pre event fields none transition contract.targets fired,
      fire_declared ids model pre event fields none transition drained.admitted.timers contract.arms fired,
      summary.2.1 drained.admitted.timed⟩
  let batch : Batch := {after := transition.after, trace := prefixBatch.trace ++ [transition]}
  have done : dispatch model s event fields limit = .ok batch := by
    simp [dispatch, allowed, advanced, drained.external_eq_fire event fields allowed, pre, fired, batch]
  refine ⟨batch, done, final, summary.1.trans drained.atLimit, ?_⟩
  exact dispatch_from_raw ids model event fields limit contract.arms contract.timerRaw
    (fun _ => raw) s admitted.timed bound admitted.valid admitted.timers batch done

/-- For a declared external event, success or the uncovered fault is determined
    by actual guard evaluation after the complete timer prefix. -/
theorem dispatch_success_or_uncovered (model : Model) (states ids : List Nat) (limit : Int)
    (contract : TimerContracts model states ids) (s : Snapshot)
    (admitted : Admitted model states ids s) (bound : s.now ≤ limit)
    (event : Nat) (fields : Values) (allowed : event ∈ model.externalEvents)
    (raw : MatchingRaw model event none) :
    ∃ prefixBatch, advance model s limit = .ok prefixBatch ∧
      Drained model states ids limit prefixBatch.after ∧
      (if (enabled model prefixBatch.after event fields).isEmpty then
        dispatch model s event fields limit = .error .uncovered ∧
          rollback s (dispatch model s event fields limit) = s
      else ∃ batch, dispatch model s event fields limit = .ok batch ∧
        Admitted model states ids batch.after ∧ batch.after.now = limit ∧
        Preserved ids model batch) := by
  obtain ⟨prefixBatch, advanced, drained, _⟩ :=
    advance_total_with_timers model states ids limit contract s admitted bound
  refine ⟨prefixBatch, advanced, drained, ?_⟩
  cases selected : enabled model prefixBatch.after event fields with
  | nil =>
    simpa [selected] using dispatch_uncovered
      model states ids limit s prefixBatch event fields allowed advanced drained selected
  | cons rule rest =>
    have member : rule ∈ enabled model prefixBatch.after event fields := by simp [selected]
    simpa [selected] using dispatch_enabled model states ids limit contract s admitted bound
      event fields allowed raw prefixBatch advanced drained ⟨rule, member⟩

theorem dispatch_total (model : Model) (states ids : List Nat) (limit : Int)
    (contract : Contracts model states ids) (s : Snapshot)
    (admitted : Admitted model states ids s) (bound : s.now ≤ limit)
    (event : Nat) (fields : Values) (allowed : event ∈ model.externalEvents) :
    ∃ batch, dispatch model s event fields limit = .ok batch ∧
      Admitted model states ids batch.after ∧ batch.after.now = limit ∧
      Preserved ids model batch := by
  obtain ⟨prefixBatch, advanced, drained, _⟩ :=
    advance_total model states ids limit contract s admitted bound
  obtain ⟨rule, member, source, trigger, guard⟩ :=
    contract.externalCoverage prefixBatch.after event fields
      drained.admitted.state allowed drained.admitted.valid
  have enabledMember : rule ∈ enabled model prefixBatch.after event fields :=
    List.mem_filter.mpr ⟨member, by simp [source, trigger, guard]⟩
  exact dispatch_enabled model states ids limit contract.timerContracts s admitted bound
    event fields allowed (contract.externalRaw event allowed) prefixBatch advanced drained
    ⟨rule, enabledMember⟩

end FormalSpecAgent.BatchTotality
