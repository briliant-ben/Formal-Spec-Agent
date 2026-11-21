import Approved
import EffectConditions
import GuardedSuffix

namespace TCPIPReceiveData
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts
open EffectConditions EffectFootprint GuardedSuffix TimedObligations
set_option maxRecDepth 16384

inductive LinkPhase where
  | empty | pending | resolved

def rule (overlap : Bool) : LinkPhase → Rule :=
  match overlap with
  | false => fun phase => match phase with
    | .empty => rule_261 | .pending => rule_262 | .resolved => rule_263
  | true => fun phase => match phase with
    | .empty => rule_264 | .pending => rule_265 | .resolved => rule_266

def linkGuard : LinkPhase → Expr .boolean
  | .empty => e16 | .pending => e35 | .resolved => e38

def dataGuard (overlap : Bool) : Expr .boolean :=
  if overlap then e1383 else e1364

def acceptedBytes (overlap : Bool) : Expr .octets :=
  if overlap then e1387 else e1368

def prefixActions (r : Rule) := r.actions.dropLast
def cut (r : Rule) : Rule := {r with actions := prefixActions r}

theorem both (s : Snapshot) (f : Values) (x y : Expr .boolean)
    (enabled : TypedMachine.eval s f (.boolAnd x y) = true) :
    TypedMachine.eval s f x = true ∧ TypedMachine.eval s f y = true := by
  change (TypedMachine.eval s f x && TypedMachine.eval s f y) = true at enabled
  simpa only [Bool.and_eq_true] using enabled

theorem data_guard_facts (s : Snapshot) (f : Values) (overlap : Bool)
    (enabled : TypedMachine.eval s f (dataGuard overlap) = true) :
    TypedMachine.eval s f e923 = true ∧ 1 ≤ TypedMachine.eval s f e1233 := by
  cases overlap
  · have input := both s f e923 e1362 (both s f e1363 e721 enabled).1
    exact ⟨input.1, of_decide_eq_true
      (both s f e1359 e1360 (both s f e1344 e1361 input.2).2).2⟩
  · have input := both s f e923 e1381 (both s f e1382 e721 enabled).1
    exact ⟨input.1, of_decide_eq_true
      (both s f e1379 e1360 (both s f e1344 e1380 input.2).2).2⟩

theorem slice_fits (data : Bytes) (offset count limit : Int)
    (nonnegative : 0 ≤ limit) (bounded : count ≤ limit) :
    (Int.ofNat (byteSlice data offset count).length) ≤ limit := by
  unfold byteSlice
  rw [List.length_take]
  have countBound : count.toNat ≤ limit.toNat := Int.toNat_le_toNat bounded
  have fit := Nat.le_trans (Nat.min_le_left count.toNat (data.drop offset.toNat).length) countBound
  exact Int.toNat_of_nonneg nonnegative ▸ Int.ofNat_le.mpr fit

theorem buffer_fits (s : Snapshot) (f : Values) (overlap : Bool)
    (room : 1 ≤ TypedMachine.eval s f e1233) :
    Int.ofNat ((TypedMachine.eval s f e932) ++
      (TypedMachine.eval s f (acceptedBytes overlap))).length ≤ 16 := by
  have nonnegative : 0 ≤ TypedMachine.eval s f e1233 := Int.le_trans (by decide : (0 : Int) ≤ 1) room
  have fits : Int.ofNat (TypedMachine.eval s f (acceptedBytes overlap)).length ≤
      TypedMachine.eval s f e1233 := by
    cases overlap
    · exact slice_fits _ _ _ _ nonnegative (Int.min_le_left ..)
    · exact slice_fits _ _ _ _ nonnegative (Int.min_le_left ..)
  rw [List.length_append]
  change Int.ofNat (TypedMachine.eval s f e932).length +
    Int.ofNat (TypedMachine.eval s f (acceptedBytes overlap)).length ≤ 16
  change Int.ofNat (TypedMachine.eval s f (acceptedBytes overlap)).length ≤
    16 - Int.ofNat (TypedMachine.eval s f e932).length at fits
  omega

abbrev checkedClause (r : Rule) (inv : Expr .boolean) (s : Snapshot) (f : Values) : Prop :=
  holds (obligationsFor (cut r) none [inv]) s f = true

theorem within_buffer (s : Snapshot) (f : Values) (overlap : Bool) (phase : LinkPhase)
    (room : 1 ≤ TypedMachine.eval s f e1233) :
    checkedClause (rule overlap phase) e1692 s f := by
  have bound := buffer_fits s f overlap room
  have checked : (decide (Int.ofNat ((TypedMachine.eval s f e932) ++
      (TypedMachine.eval s f (acceptedBytes overlap))).length ≤ 16) && true) = true := by
    rw [decide_eq_true bound]
    rfl
  cases overlap <;> cases phase <;> exact checked

theorem established_buffer (s : Snapshot) (f : Values) (overlap : Bool) (phase : LinkPhase)
    (est : TypedMachine.eval s f e923 = true) :
    checkedClause (rule overlap phase) e1698 s f := by
  cases overlap <;> cases phase <;>
    change ((!(!TypedMachine.eval s f e923) || _) && true) = true <;> simp [est]

theorem advertised_window (s : Snapshot) (f : Values) (overlap : Bool) (phase : LinkPhase) :
    checkedClause (rule overlap phase) e1699 s f := by
  let window := 16 - Int.ofNat ((TypedMachine.eval s f e932) ++
    (TypedMachine.eval s f (acceptedBytes overlap))).length
  have same : (decide (window = window) && true) = true := by simp
  cases overlap <;> cases phase <;> exact same


end TCPIPReceiveData
