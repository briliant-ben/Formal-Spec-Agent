import TimerMinimum
import TimerEffects

namespace FormalSpecAgent.TimerProgress
open TypedMachine TimerRank

theorem runRule_summary (model : Model) (s : Snapshot) (r : Rule)
    (fields : TypedIR.Values) (event : Nat) (firing : Option Nat) (t : Transition)
    (h : runRule model s r fields event firing = .ok t) :
    t.after.now = (withoutFiring s firing).now ∧
    (WellTimed (withoutFiring s firing) → WellTimed t.after) ∧
    dueCount t.after ≤ dueCount (withoutFiring s firing) := by
  unfold runRule at h
  split at h
  · contradiction
  · rename_i candidate emitted hwork
    dsimp only at h
    split at h
    · cases h
      exact TimerEffects.work_summary r.actions (withoutFiring s firing) fields [] candidate emitted hwork
    · contradiction

theorem fire_summary (model : Model) (s : Snapshot) (event : Nat)
    (fields : TypedIR.Values) (firing : Option Nat) (t : Transition)
    (h : fire model s event fields firing = .ok t) :
    t.after.now = (withoutFiring s firing).now ∧
    (WellTimed (withoutFiring s firing) → WellTimed t.after) ∧
    dueCount t.after ≤ dueCount (withoutFiring s firing) := by
  unfold fire at h
  split at h
  · contradiction
  · exact runRule_summary _ _ _ _ _ _ _ h
  · contradiction

theorem cancel_timed (s : Snapshot) (timer : Nat) (h : WellTimed s) :
    WellTimed (cancelTimer s timer) := by
  apply (wellTimed_iff _).mpr
  intro entry hmem
  have old : entry ∈ s.timers := (List.mem_filter.mp hmem).1
  exact (wellTimed_iff _).mp h entry old

private theorem remaining_drop (limit now next : Int) (hb : now ≤ limit)
    (hd : next ≤ limit) (hm : now < next) :
    (limit - next).toNat < (limit - now).toNat := by
  omega

theorem step_progress (model : Model) (snapshot : Snapshot) (limit : Int)
    (entry : TimerEntry) (transition : Transition)
    (hwell : WellTimed snapshot) (hbound : snapshot.now ≤ limit)
    (hnext : nextTimer snapshot = some entry) (hdue : entry.due ≤ limit)
    (hstep : stepTimer model snapshot entry.due = .ok transition) :
    WellTimed transition.after ∧ transition.after.now = entry.due ∧
    Prod.Lex Nat.lt Nat.lt (rank limit transition.after) (rank limit snapshot) := by
  have info := TimerMinimum.next_info snapshot entry hnext
  have ge : snapshot.now ≤ entry.due := (wellTimed_iff _).mp hwell entry info.1
  let advanced : Snapshot := { snapshot with now := entry.due }
  have timed : WellTimed advanced := by
    apply (wellTimed_iff _).mpr
    intro timer hmem
    exact info.2 timer hmem
  have notPast : ¬entry.due < snapshot.now := by omega
  have fired : fire model advanced (model.timerEvents entry.timer) zeroValues
      (some entry.timer) = .ok transition := by
    simpa [stepTimer, hnext, advanced, notPast] using hstep
  have summary := fire_summary _ _ _ _ _ _ fired
  have nowEq : transition.after.now = entry.due := summary.1
  have finalTimed : WellTimed transition.after :=
    summary.2.1 (cancel_timed advanced entry.timer timed)
  have drop := TimerEffects.cancel_count_lt advanced entry info.1 (by simp [advanced])
  have countLt : dueCount transition.after < dueCount advanced := by
    have le := summary.2.2
    change dueCount transition.after ≤ dueCount (cancelTimer advanced entry.timer) at le
    omega
  refine ⟨finalTimed, nowEq, ?_⟩
  apply Prod.lex_def.mpr
  by_cases moved : snapshot.now < entry.due
  · left
    simp only [rank, Prod.fst]
    rw [nowEq]
    exact remaining_drop limit snapshot.now entry.due hbound hdue moved
  · have same : entry.due = snapshot.now := by omega
    right
    constructor
    · simp [rank, nowEq, same]
    · simpa [rank, advanced, same] using countLt

end FormalSpecAgent.TimerProgress
