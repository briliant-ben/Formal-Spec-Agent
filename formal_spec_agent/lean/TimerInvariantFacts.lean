import TypedMachine

namespace FormalSpecAgent.TimerInvariantFacts
open TypedMachine TypedIR

/-- Expressions observe timer activity through membership only. -/
theorem sameActiveTimers {kind : Kind} (e : Expr kind) (ctx : Context) (timers : List Nat)
    (membership : ∀ id, id ∈ timers ↔ id ∈ ctx.activeTimers) :
    TypedIR.eval e { ctx with activeTimers := timers } = TypedIR.eval e ctx := by
  induction e with
  | timerActive id =>
    simp only [TypedIR.eval, membership id]
  | _ => simp_all [TypedIR.eval]

theorem cancelActive (snapshot : Snapshot) (owner id : Nat) :
    id ∈ (cancelTimer snapshot owner).timers.map TimerEntry.timer ↔
      id ∈ snapshot.timers.map TimerEntry.timer ∧ id ≠ owner := by
  constructor
  · intro h
    obtain ⟨entry, member, same⟩ := List.mem_map.mp h
    have stay := List.mem_filter.mp member
    refine ⟨List.mem_map.mpr ⟨entry, stay.1, same⟩, ?_⟩
    simpa [same] using stay.2
  · intro ⟨member, distinct⟩
    obtain ⟨entry, present, same⟩ := List.mem_map.mp member
    exact List.mem_map.mpr ⟨entry, List.mem_filter.mpr ⟨present, by simpa [same] using distinct⟩, same⟩

theorem armActive (snapshot after : Snapshot) (owner id : Nat) (delay : Int)
    (armed : armTimer snapshot owner delay = .ok after) :
    id ∈ after.timers.map TimerEntry.timer ↔ id = owner ∨ id ∈ snapshot.timers.map TimerEntry.timer := by
  unfold armTimer at armed
  split at armed
  · contradiction
  · have formed := Except.ok.inj armed
    rw [← formed]
    change id ∈ ((cancelTimer snapshot owner).timers ++ [TimerEntry.mk owner (snapshot.now + delay)]).map
        TimerEntry.timer ↔ _
    rw [List.map_append, List.mem_append, cancelActive]
    simp only [List.map_cons, List.map_nil, List.mem_singleton]
    by_cases own : id = owner <;> simp [own]

/-- Canceling the firing and rearming the same active timer preserves the
activity of every timer, including timers that share its deadline. -/
theorem rearmed_invariants (model : Model) (snapshot after : Snapshot)
    (owner : Nat) (delay : Int)
    (active : owner ∈ snapshot.timers.map TimerEntry.timer)
    (armed : armTimer (cancelTimer snapshot owner) owner delay = .ok after)
    (valid : invariantsHold model snapshot = true) :
    invariantsHold model after = true := by
  have membership (id : Nat) :
      id ∈ after.timers.map TimerEntry.timer ↔ id ∈ snapshot.timers.map TimerEntry.timer := by
    rw [armActive _ _ _ _ _ armed, cancelActive]
    by_cases same : id = owner
    · subst id
      simp [active]
    · simp [same]
  have afterContext : context after zeroValues =
      { context snapshot zeroValues with activeTimers := after.timers.map TimerEntry.timer } := by
    unfold armTimer at armed
    split at armed
    · contradiction
    · rw [← Except.ok.inj armed]
      rfl
  apply List.all_eq_true.mpr
  intro inv member
  unfold TypedMachine.eval
  rw [afterContext, sameActiveTimers inv _ _ membership]
  exact List.all_eq_true.mp valid inv member

end FormalSpecAgent.TimerInvariantFacts
