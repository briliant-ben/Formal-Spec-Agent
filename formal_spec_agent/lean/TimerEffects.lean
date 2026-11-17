import TimerRank

namespace FormalSpecAgent.TimerEffects
open TypedMachine TimerRank

private theorem cancel_count (s : Snapshot) (timer : Nat) :
    dueCount (cancelTimer s timer) =
    ((s.timers.filter fun e => decide (e.due ≤ s.now)).filter fun e => e.timer != timer).length := by
  simp [dueCount, cancelTimer, List.filter_filter, Bool.and_comm]
  rfl

theorem cancel_count_le (s : Snapshot) (timer : Nat) :
    dueCount (cancelTimer s timer) ≤ dueCount s := by
  rw [cancel_count]
  exact List.length_filter_le _ _

theorem cancel_count_lt (s : Snapshot) (entry : TimerEntry)
    (hmem : entry ∈ s.timers) (hdue : entry.due ≤ s.now) :
    dueCount (cancelTimer s entry.timer) < dueCount s := by
  rw [cancel_count]
  apply List.length_filter_lt_length_iff_exists.mpr
  refine ⟨entry, ?_, ?_⟩
  · exact List.mem_filter.mpr ⟨hmem, by simpa using hdue⟩
  · simp

theorem cancel_timed (s : Snapshot) (timer : Nat) (h : WellTimed s) :
    WellTimed (cancelTimer s timer) := by
  apply (wellTimed_iff _).mpr
  intro entry member
  exact (wellTimed_iff _).mp h entry (List.mem_filter.mp member).1

private theorem arm_summary (s : Snapshot) (timer : Nat) (delay : Int)
    (after : Snapshot) (h : armTimer s timer delay = .ok after) :
    after.now = s.now ∧ (WellTimed s → WellTimed after) ∧ dueCount after ≤ dueCount s := by
  unfold armTimer at h
  split at h
  · contradiction
  · rename_i positive
    cases h
    have future : ¬s.now + delay ≤ s.now := by omega
    constructor
    · rfl
    · constructor
      · intro timed
        apply (wellTimed_iff _).mpr
        intro entry member
        rcases List.mem_append.mp member with old | new
        · exact (wellTimed_iff _).mp timed entry (List.mem_filter.mp old).1
        · have eq := List.mem_singleton.mp new
          subst entry
          dsimp only
          omega
      · have countEq : dueCount
            { s with timers := s.timers.filter (fun te => te.timer != timer) ++
                [{ timer := timer, due := s.now + delay }] } =
            dueCount (cancelTimer s timer) := by
          simp [dueCount, cancelTimer, List.filter_append, future]
          rfl
        rw [countEq]
        exact cancel_count_le s timer

theorem work_summary (actions : List Action) (s : Snapshot) (fields : TypedIR.Values)
    (outputs : List Message) (after : Snapshot) (emitted : List Message)
    (h : work actions s fields outputs = .ok (after,emitted)) :
    after.now = s.now ∧ (WellTimed s → WellTimed after) ∧ dueCount after ≤ dueCount s := by
  induction actions generalizing s outputs with
  | nil =>
    simp only [work, Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨rfl, fun p => p, Nat.le_refl _⟩
  | cons action rest ih =>
    cases action with
    | assign kind slot expression =>
      exact ih { s with values := setValue kind slot (eval s fields expression) s.values } outputs h
    | emit message fieldsExpr =>
      let evaluated : List FieldValue := fieldsExpr.map (fun fe =>
        { slot := fe.slot, kind := fe.kind, value := eval s fields fe.expression })
      let msg : Message := { name := message, fields := evaluated }
      exact ih s (outputs ++ [msg]) h
    | cancel timer =>
      have result := ih (cancelTimer s timer) outputs h
      exact ⟨result.1, fun timed => result.2.1 (cancel_timed s timer timed),
        Nat.le_trans result.2.2 (cancel_count_le s timer)⟩
    | arm timer delay =>
      simp only [work] at h
      cases ha : armTimer s timer (eval s fields delay) with
      | error fault => simp only [ha] at h; contradiction
      | ok middle =>
        simp only [ha] at h
        have first := arm_summary _ _ _ _ ha
        have second := ih middle outputs h
        refine ⟨second.1.trans first.1, fun p => second.2.1 (first.2.1 p), ?_⟩
        exact Nat.le_trans second.2.2 first.2.2

end FormalSpecAgent.TimerEffects
