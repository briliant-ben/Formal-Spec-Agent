import TypedIR

namespace FormalSpecAgent.OctetBounds
open TypedIR

private def constantCount : Expr .integer → Option Nat
  | .literal _ n => some n.toNat
  | _ => none

private theorem count_sound (count : Expr .integer) (ctx : Context) (n : Nat)
    (found : constantCount count = some n) : (eval count ctx).toNat = n := by
  cases count <;> simp [constantCount, eval] at found ⊢
  exact found

/-- Static upper bounds on octet count. A variable or field may have any
length. A slice with constant count is bounded even when its inputs vary. -/
def upper (expr : Expr kind) : Option Nat :=
  match expr with
  | .literal .octets bytes => some bytes.length
  | .concat left right => return (← upper left) + (← upper right)
  | .choose .octets _ yes no => return max (← upper yes) (← upper no)
  | .slice bytes _ count =>
    match constantCount count with
    | some n => some n
    | none => upper bytes
  | .pack8 _ => some 1
  | .pack16 _ => some 2
  | .pack32 _ => some 4
  | _ => none
termination_by structural expr

theorem sound (expr : Expr .octets) (ctx : Context) (limit : Nat)
    (checked : upper expr = some limit) : (eval expr ctx).length ≤ limit := by
  match expr with
  | .variable .. | .field .. => simp [upper] at checked
  | .literal _ bytes =>
    have eq : bytes.length = limit := by simpa [upper] using checked
    exact Nat.le_of_eq eq
  | .pack8 _ => simp [upper] at checked; subst limit; exact Nat.le_refl _
  | .pack16 _ => simp [upper] at checked; subst limit; exact Nat.le_refl _
  | .pack32 _ => simp [upper] at checked; subst limit; exact Nat.le_refl _
  | .concat a b =>
    cases ha : upper a with
    | none => simp [upper, ha] at checked
    | some x =>
      cases hb : upper b with
      | none => simp [upper, ha, hb] at checked
      | some y =>
        have limitEq : x + y = limit := by simpa [upper, ha, hb] using checked
        rw [← limitEq]
        change ((eval a ctx) ++ (eval b ctx)).length ≤ x + y
        rw [List.length_append]
        exact Nat.add_le_add (sound a ctx x ha) (sound b ctx y hb)
  | .choose _ condition a b =>
    cases ha : upper a with
    | none => simp [upper, ha] at checked
    | some x =>
      cases hb : upper b with
      | none => simp [upper, ha, hb] at checked
      | some y =>
        have limitEq : max x y = limit := by simpa [upper, ha, hb] using checked
        rw [← limitEq]
        change (if eval condition ctx then eval a ctx else eval b ctx).length ≤ max x y
        split
        · exact Nat.le_trans (sound a ctx x ha) (Nat.le_max_left ..)
        · exact Nat.le_trans (sound b ctx y hb) (Nat.le_max_right ..)
  | .slice data offset count =>
    change (byteSlice (eval data ctx) (eval offset ctx) (eval count ctx)).length ≤ limit
    rw [byteSlice, List.length_take]
    cases known : constantCount count with
    | some n =>
      have limitEq : n = limit := by simpa [upper, known] using checked
      rw [count_sound count ctx n known, limitEq]
      exact Nat.min_le_left ..
    | none =>
      have bound : upper data = some limit := by simpa [upper, known] using checked
      rw [List.length_drop]
      exact Nat.le_trans (Nat.min_le_right ..) (Nat.le_trans (Nat.sub_le ..) (sound data ctx limit bound))
termination_by sizeOf expr

/-- Length contributed by statically sized parts, independent of their bytes. -/
def lower (expr : Expr kind) : Nat :=
  match expr with
  | .literal .octets bytes => bytes.length
  | .concat left right => lower left + lower right
  | .choose .octets _ yes no => min (lower yes) (lower no)
  | .slice data offset count =>
    match constantCount offset, constantCount count with
    | some skip, some take => min take (lower data - skip)
    | _, _ => 0
  | .pack8 _ => 1
  | .pack16 _ => 2
  | .pack32 _ => 4
  | _ => 0
termination_by structural expr

theorem lower_sound (expr : Expr .octets) (ctx : Context) :
    lower expr ≤ (eval expr ctx).length := by
  match expr with
  | .concat a b =>
    change lower a + lower b ≤ ((eval a ctx) ++ (eval b ctx)).length
    rw [List.length_append]
    exact Nat.add_le_add (lower_sound a ctx) (lower_sound b ctx)
  | .choose _ condition yes no =>
    change min (lower yes) (lower no) ≤ (if eval condition ctx then eval yes ctx else eval no ctx).length
    split
    · exact Nat.le_trans (Nat.min_le_left ..) (lower_sound yes ctx)
    · exact Nat.le_trans (Nat.min_le_right ..) (lower_sound no ctx)
  | .literal .. | .pack8 .. | .pack16 .. | .pack32 .. => exact Nat.le_refl _
  | .variable .. | .field .. => exact Nat.zero_le _
  | .slice data offset count =>
    cases hOffset : constantCount offset <;> cases hCount : constantCount count
    all_goals try (simp [lower, hOffset, hCount]; done)
    rename_i skip take
    have a := count_sound offset ctx skip hOffset
    have b := count_sound count ctx take hCount
    have len := lower_sound data ctx
    change lower (.slice data offset count) ≤ (byteSlice (eval data ctx) (eval offset ctx) (eval count ctx)).length
    simp only [lower, hOffset, hCount, byteSlice, List.length_take, List.length_drop, a, b]
    omega
termination_by sizeOf expr

/-- Check a length inequality without evaluating any packet contents. -/
def certifies : Expr .boolean → Bool
  | .intLe (.bytesLength bytes) (.literal _ n) =>
    match upper bytes with
    | some size => decide ((size : Int) ≤ n)
    | none => false
  | .intGe (.literal _ lhs) (.literal _ rhs) => decide (rhs ≤ lhs)
  | _ => false

private theorem length_inequality (bytes : Expr .octets) (n : Int) (ctx : Context)
    (accepted : certifies (.intLe (.bytesLength bytes) (.literal .integer n)) = true) :
    eval (.intLe (.bytesLength bytes) (.literal .integer n)) ctx = true := by
  cases bound : upper bytes with
  | none => simp [certifies, bound] at accepted
  | some size =>
    have value : ((size : Int) ≤ n) := by simpa [certifies, bound] using accepted
    have length : (eval bytes ctx).length ≤ size := sound bytes ctx size bound
    exact decide_eq_true (Int.le_trans (Int.ofNat_le.mpr length) value)

theorem certifies_sound (e : Expr .boolean) (ctx : Context)
    (accepted : certifies e = true) : eval e ctx = true := by
  cases e with
  | intLe lhs rhs =>
    cases lhs <;> cases rhs <;> first
    | exact length_inequality _ _ ctx accepted
    | simp [certifies] at accepted
  | intGe lhs rhs =>
    cases lhs <;> cases rhs <;> simp [certifies, eval] at accepted ⊢
    exact accepted
  | _ => simp [certifies] at accepted

theorem all_sound (checks : List (Expr .boolean)) (ctx : Context)
    (accepted : checks.all certifies = true) : checks.all (fun e => eval e ctx) = true := by
  apply List.all_eq_true.mpr
  intro e member
  exact certifies_sound e ctx (List.all_eq_true.mp accepted e member)

end FormalSpecAgent.OctetBounds
