import TypedMachine

namespace FormalSpecAgent.StoreFacts

theorem function_update_shadow (index : Nat) (x y : α) (tail : Nat → α) :
    (fun n => if n = index then x else if n = index then y else tail n) =
    (fun n => if n = index then x else tail n) := by
  funext n
  by_cases h : n = index <;> simp [h]

theorem function_update_order (lo hi : Nat) (ordered : lo < hi) (x y : α) (tail : Nat → α) :
    (fun n => if n = hi then y else if n = lo then x else tail n) =
    (fun n => if n = lo then x else if n = hi then y else tail n) := by
  funext n
  by_cases a : n = lo
  · subst n
    have ne : lo ≠ hi := by omega
    simp [ne]
  · have reverse : hi ≠ lo := by omega
    by_cases b : n = hi <;> simp [a, b, reverse]

theorem function_cond_constant (index : Nat) (value fallback : α) :
    ((fun n => if n = index then value else fallback) = fun _ => fallback) ↔
    value = fallback := by
  constructor
  · intro h
    have atIndex := congrFun h index
    simpa using atIndex
  · intro h
    simp [h]

theorem serial_wrap :
    ValueOps.seqAdd (⟨4294967295, by decide⟩ : ValueOps.Seq32) 1 =
    (⟨0, by decide⟩ : ValueOps.Seq32) := by
  decide

theorem serial_wrap_from_value (s : ValueOps.Seq32) (h : s.val = 4294967295) :
    ValueOps.seqAdd s 1 = (⟨0, by decide⟩ : ValueOps.Seq32) := by
  apply Fin.ext
  simp only [ValueOps.seqAdd, h]
  decide

/-- Canonical order for independent boolean slots after simplification. -/
theorem function_bool_or_order (lo hi : Nat) (_h : lo < hi) :
    (fun n => decide (n = hi) || decide (n = lo)) =
      (fun n => decide (n = lo) || decide (n = hi)) := by
  funext n
  exact Bool.or_comm _ _

/-- Clearing one boolean slot does not disturb a distinct true slot. -/
theorem function_bool_remove (lo hi : Nat) (h : lo ≠ hi) :
    (fun n => !decide (n = hi) && (decide (n = lo) || decide (n = hi))) =
      (fun n => decide (n = lo)) := by
  funext n
  by_cases hn : n = hi
  · subst n
    simp_all [Ne.symm h]
  · simp [hn]

end FormalSpecAgent.StoreFacts
