import TimerRank

namespace FormalSpecAgent.TimerMinimum
open TypedMachine

private def pick (best entry : TimerEntry) : TimerEntry :=
  if entry.due < best.due ∨ (entry.due = best.due ∧ entry.timer < best.timer)
  then entry else best

private def scan (best : TimerEntry) : List TimerEntry → TimerEntry
  | [] => best
  | entry :: rest => scan (pick best entry) rest

private theorem scan_spec (xs : List TimerEntry) (best : TimerEntry) :
    scan best xs ∈ best :: xs ∧ (scan best xs).due ≤ best.due ∧
    ∀ entry ∈ xs, (scan best xs).due ≤ entry.due := by
  induction xs generalizing best with
  | nil => simp [scan]
  | cons head tail ih =>
    have sub := ih (pick best head)
    have chosen : pick best head = best ∨ pick best head = head := by
      unfold pick
      split <;> simp
    have leBest : (pick best head).due ≤ best.due := by
      unfold pick
      split <;> omega
    have leHead : (pick best head).due ≤ head.due := by
      unfold pick
      split <;> omega
    change scan (pick best head) tail ∈ best :: head :: tail ∧
      (scan (pick best head) tail).due ≤ best.due ∧
      ∀ entry ∈ head :: tail, (scan (pick best head) tail).due ≤ entry.due
    constructor
    · have membership := sub.1
      simp only [List.mem_cons] at membership ⊢
      rcases membership with eq | rest
      · rcases chosen with hb | hh
        · exact Or.inl (eq.trans hb)
        · exact Or.inr (Or.inl (eq.trans hh))
      · exact Or.inr (Or.inr rest)
    · constructor
      · have lower := sub.2.1
        omega
      · intro entry member
        rcases List.mem_cons.mp member with eq | rest
        · subst entry
          have lower := sub.2.1
          omega
        · exact sub.2.2 entry rest

private def optionPick (best : Option TimerEntry) (entry : TimerEntry) : Option TimerEntry :=
  match best with
  | none => some entry
  | some b => if entry.due < b.due ∨ (entry.due = b.due ∧ entry.timer < b.timer)
      then some entry else best

private theorem fold_some (xs : List TimerEntry) (best : TimerEntry) :
    xs.foldl optionPick (some best) = some (scan best xs) := by
  induction xs generalizing best with
  | nil => rfl
  | cons head tail ih =>
    change tail.foldl optionPick (optionPick (some best) head) =
      some (scan (pick best head) tail)
    by_cases h : head.due < best.due ∨ (head.due = best.due ∧ head.timer < best.timer)
    · simpa only [optionPick, pick, if_pos h] using ih head
    · simpa only [optionPick, pick, if_neg h] using ih best

theorem next_info (s : Snapshot) (entry : TimerEntry) (h : nextTimer s = some entry) :
    entry ∈ s.timers ∧ ∀ timer ∈ s.timers, entry.due ≤ timer.due := by
  cases ht : s.timers with
  | nil => simp [nextTimer, ht] at h
  | cons head tail =>
    have folded : nextTimer s = some (scan head tail) := by
      change s.timers.foldl optionPick none = _
      rw [ht]
      change tail.foldl optionPick (some head) = _
      exact fold_some tail head
    have eq : scan head tail = entry := Option.some.inj (folded.symm.trans h)
    subst entry
    have summary := scan_spec tail head
    constructor
    · simpa only [ht] using summary.1
    · intro timer member
      rcases List.mem_cons.mp member with same | rest
      · subst timer
        exact summary.2.1
      · exact summary.2.2 timer rest

end FormalSpecAgent.TimerMinimum
