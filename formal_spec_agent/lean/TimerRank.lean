import TypedMachine

namespace FormalSpecAgent.TimerRank
open TypedMachine

abbrev WellTimed (s : Snapshot) : Prop :=
  s.timers.all (fun entry => decide (s.now ≤ entry.due)) = true

instance (s : Snapshot) : Decidable (WellTimed s) :=
  inferInstanceAs (Decidable (s.timers.all (fun entry => decide (s.now ≤ entry.due)) = true))

def dueCount (s : Snapshot) : Nat :=
  (s.timers.filter fun entry => decide (entry.due ≤ s.now)).length

def rank (limit : Int) (s : Snapshot) : Nat × Nat :=
  ((limit - s.now).toNat, dueCount s)

theorem wellTimed_iff (s : Snapshot) :
    WellTimed s ↔ ∀ entry ∈ s.timers, s.now ≤ entry.due := by
  simp [WellTimed, List.all_eq_true]

end FormalSpecAgent.TimerRank
