import BatchPreservation

namespace FormalSpecAgent.TimedSelection
open TypedMachine TypedIR TypedContracts TypedFiringContracts
open ScheduledPreservation TimerDomain TimerMinimum

/-- Coverage at a timer firing uses its empty event environment and tests the
    guard before removing the fired timer, as the actual dispatcher does. -/
def CoversTimers (model : Model) (states ids : List Nat) : Prop :=
  ∀ s, s.state ∈ states → invariantsHold model s = true →
    ∀ entry ∈ s.timers, entry.timer ∈ ids →
      ∃ r ∈ model.rules, r.source = s.state ∧ r.event = model.timerEvents entry.timer ∧
        eval s zeroValues r.guard = true

theorem enabled_singleton (model : Model) (s : Snapshot) (event : Nat) (fields : Values)
    (unique : (model.rules.map Rule.id).Nodup) (disjoint : GuardsDisjoint model)
    (valid : invariantsHold model s = true)
    (existsEnabled : ∃ r, r ∈ enabled model s event fields) :
    ∃ r, enabled model s event fields = [r] := by
  have ordered : ((enabled model s event fields).map Rule.id).Nodup :=
    List.Nodup.sublist (List.filter_sublist.map _) unique
  cases selected : enabled model s event fields with
  | nil => simp [selected] at existsEnabled
  | cons first rest =>
    cases rest with
    | nil => exact ⟨first, rfl⟩
    | cons second tail =>
      have distinct : first.id ≠ second.id := by
        intro equal
        rw [selected] at ordered
        have missing := (List.nodup_cons.mp ordered).1
        apply missing
        simp [equal]
      have one : first ∈ enabled model s event fields := by simp [selected]
      have two : second ∈ enabled model s event fields := by simp [selected]
      have left := List.mem_filter.mp one
      have right := List.mem_filter.mp two
      simp only [Bool.and_eq_true, beq_iff_eq] at left right
      rcases disjoint s fields valid event first second left.1 right.1 distinct
          left.2.1.1 right.2.1.1 left.2.1.2 right.2.1.2 with bad | bad
      · rw [left.2.2] at bad
        contradiction
      · rw [right.2.2] at bad
        contradiction

theorem fire_enabled_from_raw (model : Model) (s : Snapshot) (event : Nat)
    (fields : Values) (firing : Option Nat)
    (unique : (model.rules.map Rule.id).Nodup) (disjoint : GuardsDisjoint model)
    (valid : invariantsHold model s = true) (raw : MatchingRaw model event firing)
    (existsEnabled : ∃ r ∈ model.rules, r.source = s.state ∧ r.event = event ∧
      eval s fields r.guard = true) :
    ∃ t, fire model s event fields firing = .ok t ∧ invariantsHold model t.after = true := by
  have covered : ∃ r, r ∈ enabled model s event fields := by
    obtain ⟨rule, member, source, trigger, guard⟩ := existsEnabled
    exact ⟨rule, List.mem_filter.mpr ⟨member, by simp [source, trigger, guard]⟩⟩
  obtain ⟨rule, selected⟩ := enabled_singleton model s event fields unique disjoint valid covered
  have member : rule ∈ enabled model s event fields := by simp [selected]
  have facts := List.mem_filter.mp member
  simp only [Bool.and_eq_true, beq_iff_eq] at facts
  exact fire_singleton_succeeds model s event fields firing rule selected
    (raw rule facts.1 facts.2.1.2) valid facts.2.1.1.symm facts.2.2

theorem timer_enabled_from_contracts (model : Model) (states ids : List Nat)
    (s : Snapshot) (entry : TimerEntry)
    (unique : (model.rules.map Rule.id).Nodup) (disjoint : GuardsDisjoint model)
    (covered : CoversTimers model states ids)
    (raw : BatchPreservation.TimerRaw ids model)
    (valid : invariantsHold model s = true) (declared : Declared ids s)
    (state : s.state ∈ states) (next : nextTimer s = some entry)
    (timed : s.now ≤ entry.due) :
    ∃ t, stepTimer model s entry.due = .ok t ∧ invariantsHold model t.after = true := by
  have member := (next_info s entry next).1
  have timer := declared entry member
  let pre := {s with now := entry.due}
  have beforeValid : invariantsHold model pre = true :=
    (invariants_clock_irrelevant model s entry.due).symm.trans valid
  obtain ⟨t, fired, afterValid⟩ :=
    fire_enabled_from_raw model pre (model.timerEvents entry.timer) zeroValues (some entry.timer)
      unique disjoint beforeValid (raw entry.timer timer)
      (covered pre state beforeValid entry member timer)
  exact ⟨t, by simpa [stepTimer, next, Int.not_lt.mpr timed, pre] using fired, afterValid⟩

theorem external_enabled_from_contracts (model : Model) (states : List Nat)
    (s : Snapshot) (event : Nat) (fields : Values) (time : Int)
    (unique : (model.rules.map Rule.id).Nodup) (disjoint : GuardsDisjoint model)
    (covered : Covers model states) (raw : MatchingRaw model event none)
    (valid : invariantsHold model s = true) (state : s.state ∈ states)
    (declared : event ∈ model.externalEvents) (timed : s.now ≤ time)
    (noDue : (match nextTimer s with
      | some entry => decide (entry.due ≤ time)
      | none => false) = false) :
    ∃ t, external model s event fields time = .ok t ∧ invariantsHold model t.after = true := by
  let pre := {s with now := time}
  have beforeValid : invariantsHold model pre = true :=
    (invariants_clock_irrelevant model s time).symm.trans valid
  obtain ⟨t, fired, afterValid⟩ :=
    fire_enabled_from_raw model pre event fields none unique disjoint beforeValid raw
      (covered pre event fields state declared beforeValid)
  refine ⟨t, ?_, afterValid⟩
  cases selected : nextTimer s with
  | none => simpa [external, Int.not_lt.mpr timed, declared, selected, pre] using fired
  | some entry =>
    have late : ¬ entry.due ≤ time := by simpa [selected] using noDue
    simpa [external, Int.not_lt.mpr timed, declared, selected, late, pre] using fired

end FormalSpecAgent.TimedSelection
