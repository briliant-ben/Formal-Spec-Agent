import TypedFiringContracts
import TimerMinimum

namespace FormalSpecAgent.ScheduledPreservation
open TypedMachine TypedIR TypedFiringContracts TimerMinimum

/-- Every matching rule must satisfy the raw, unfiltered firing contract. -/
def MatchingRaw (model : Model) (event : Nat) (firing : Option Nat) : Prop :=
  ∀ r ∈ model.rules, r.event = event → FiringPreserves model r firing

theorem fire_success_invariant_from_raw (model : Model) (snapshot : Snapshot) (event : Nat)
    (fields : Values) (firing : Option Nat) (t : Transition)
    (hRaw : MatchingRaw model event firing)
    (hInv : invariantsHold model snapshot = true)
    (hFire : fire model snapshot event fields firing = .ok t) :
    invariantsHold model t.after = true := by
  unfold fire at hFire
  cases hEnabled : enabled model snapshot event fields with
  | nil => simp only [hEnabled] at hFire; contradiction
  | cons r rest =>
    cases hRest : rest with
    | nil =>
      have hOne : enabled model snapshot event fields = [r] := by rw [hEnabled, hRest]
      have hMember : r ∈ enabled model snapshot event fields := by
        rw [hOne]
        exact List.mem_singleton_self r
      have selected := List.mem_filter.mp hMember
      have facts := selected.2
      simp only [Bool.and_eq_true, beq_iff_eq] at facts
      have hEvent : r.event = event := facts.1.2
      obtain ⟨actual, hRun, hAfter⟩ := preserving_firing_succeeds model r snapshot fields firing
        (hRaw r selected.1 hEvent) hInv facts.1.1.symm facts.2
      rw [hEvent] at hRun
      simp only [hOne] at hFire
      have equal : actual = t := Except.ok.inj (hRun.symm.trans hFire)
      simpa only [equal] using hAfter
    | cons other tail =>
      simp only [hEnabled, hRest] at hFire
      contradiction

theorem external_success_invariant_from_raw (model : Model) (snapshot : Snapshot) (event : Nat)
    (fields : Values) (time : Int) (t : Transition)
    (hRaw : event ∈ model.externalEvents → MatchingRaw model event none)
    (hInv : invariantsHold model snapshot = true)
    (hExternal : external model snapshot event fields time = .ok t) :
    invariantsHold model t.after = true := by
  unfold external at hExternal
  split at hExternal
  · contradiction
  · split at hExternal
    · contradiction
    · rename_i allowed
      have member : event ∈ model.externalEvents := by simpa using allowed
      split at hExternal
      · split at hExternal
        · contradiction
        · exact fire_success_invariant_from_raw model {snapshot with now := time} event fields none t
            (hRaw member) (by simpa only [← invariants_clock_irrelevant model snapshot time] using hInv)
            hExternal
      · exact fire_success_invariant_from_raw model {snapshot with now := time} event fields none t
          (hRaw member) (by simpa only [← invariants_clock_irrelevant model snapshot time] using hInv)
          hExternal

theorem timer_success_invariant_from_raw (model : Model) (snapshot : Snapshot) (time : Int)
    (t : Transition)
    (hRaw : ∀ entry ∈ snapshot.timers,
      MatchingRaw model (model.timerEvents entry.timer) (some entry.timer))
    (hInv : invariantsHold model snapshot = true)
    (hStep : stepTimer model snapshot time = .ok t) :
    invariantsHold model t.after = true := by
  unfold stepTimer at hStep
  split at hStep
  · contradiction
  · cases hNext : nextTimer snapshot with
    | none => simp only [hNext] at hStep; contradiction
    | some entry =>
      simp only [hNext] at hStep
      split at hStep
      · contradiction
      · exact fire_success_invariant_from_raw model {snapshot with now := time}
          (model.timerEvents entry.timer) zeroValues (some entry.timer) t
          (hRaw entry (next_info snapshot entry hNext).1)
          (by simpa only [← invariants_clock_irrelevant model snapshot time] using hInv)
          hStep

end FormalSpecAgent.ScheduledPreservation
