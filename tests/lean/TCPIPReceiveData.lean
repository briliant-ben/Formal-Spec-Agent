import Approved
import EffectConditions
import GuardedSuffix

namespace TCPIPReceiveData
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts
open EffectConditions EffectFootprint GuardedSuffix TimedObligations
set_option maxRecDepth 16384

private inductive LinkPhase where
  | empty | pending | resolved

private def rule (overlap : Bool) : LinkPhase → Rule :=
  match overlap with
  | false => fun phase => match phase with
    | .empty => rule_261 | .pending => rule_262 | .resolved => rule_263
  | true => fun phase => match phase with
    | .empty => rule_264 | .pending => rule_265 | .resolved => rule_266

private def linkGuard : LinkPhase → Expr .boolean
  | .empty => e16 | .pending => e35 | .resolved => e38

private def dataGuard (overlap : Bool) : Expr .boolean :=
  if overlap then e1383 else e1364

private def acceptedBytes (overlap : Bool) : Expr .octets :=
  if overlap then e1387 else e1368

private def prefixActions (r : Rule) := r.actions.dropLast
private def cut (r : Rule) : Rule := {r with actions := prefixActions r}

private theorem both (s : Snapshot) (f : Values) (x y : Expr .boolean)
    (enabled : TypedMachine.eval s f (.boolAnd x y) = true) :
    TypedMachine.eval s f x = true ∧ TypedMachine.eval s f y = true := by
  change (TypedMachine.eval s f x && TypedMachine.eval s f y) = true at enabled
  simpa only [Bool.and_eq_true] using enabled

private theorem data_guard_facts (s : Snapshot) (f : Values) (overlap : Bool)
    (enabled : TypedMachine.eval s f (dataGuard overlap) = true) :
    TypedMachine.eval s f e923 = true ∧ 1 ≤ TypedMachine.eval s f e1233 := by
  cases overlap
  · have input := both s f e923 e1362 (both s f e1363 e721 enabled).1
    exact ⟨input.1, of_decide_eq_true
      (both s f e1359 e1360 (both s f e1344 e1361 input.2).2).2⟩
  · have input := both s f e923 e1381 (both s f e1382 e721 enabled).1
    exact ⟨input.1, of_decide_eq_true
      (both s f e1379 e1360 (both s f e1344 e1380 input.2).2).2⟩

private theorem slice_fits (data : Bytes) (offset count limit : Int)
    (nonnegative : 0 ≤ limit) (bounded : count ≤ limit) :
    (Int.ofNat (byteSlice data offset count).length) ≤ limit := by
  unfold byteSlice
  rw [List.length_take]
  have countBound : count.toNat ≤ limit.toNat := Int.toNat_le_toNat bounded
  have fit := Nat.le_trans (Nat.min_le_left count.toNat (data.drop offset.toNat).length) countBound
  exact Int.toNat_of_nonneg nonnegative ▸ Int.ofNat_le.mpr fit

private theorem buffer_fits (s : Snapshot) (f : Values) (overlap : Bool)
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

private abbrev checkedClause (r : Rule) (inv : Expr .boolean) (s : Snapshot) (f : Values) : Prop :=
  holds (obligationsFor (cut r) none [inv]) s f = true

private theorem within_buffer (s : Snapshot) (f : Values) (overlap : Bool) (phase : LinkPhase)
    (room : 1 ≤ TypedMachine.eval s f e1233) :
    checkedClause (rule overlap phase) e1692 s f := by
  have bound := buffer_fits s f overlap room
  have checked : (decide (Int.ofNat ((TypedMachine.eval s f e932) ++
      (TypedMachine.eval s f (acceptedBytes overlap))).length ≤ 16) && true) = true := by
    rw [decide_eq_true bound]
    rfl
  cases overlap <;> cases phase <;> exact checked

private theorem established_buffer (s : Snapshot) (f : Values) (overlap : Bool) (phase : LinkPhase)
    (est : TypedMachine.eval s f e923 = true) :
    checkedClause (rule overlap phase) e1698 s f := by
  cases overlap <;> cases phase <;>
    change ((!(!TypedMachine.eval s f e923) || _) && true) = true <;> simp [est]

private theorem advertised_window (s : Snapshot) (f : Values) (overlap : Bool) (phase : LinkPhase) :
    checkedClause (rule overlap phase) e1699 s f := by
  let window := 16 - Int.ofNat ((TypedMachine.eval s f e932) ++
    (TypedMachine.eval s f (acceptedBytes overlap))).length
  have same : (decide (window = window) && true) = true := by simp
  cases overlap <;> cases phase <;> exact same

set_option maxHeartbeats 1000000 in
private theorem packet_bound (s : Snapshot) (f : Values) (overlap : Bool) (phase : LinkPhase) :
    checkedClause (rule overlap phase) e1706 s f := by
  cases overlap <;> cases phase <;> rfl

private def affected : LinkPhase → List (Expr .boolean)
  | .empty => [e1594, e1597, e1601, e1604, e1612, e1614, e1615, e1628,
               e1692, e1698, e1699, e1706, e1721]
  | .pending => [e1612, e1614, e1615, e1692, e1698, e1699, e1706, e1721]
  | .resolved => [e1692, e1698, e1699, e1706]

private theorem empty_cache (s : Snapshot) (f : Values) (overlap : Bool)
    (initiallyEmpty : TypedMachine.eval s f e16 = true)
    (valid : invariantsHold model s = true) :
    checkedClause (rule overlap .empty) e1597 s f := by
  have before := List.all_eq_true.mp valid e1594 (by rw [model_invariants]; simp)
  have empty : TypedMachine.eval s zeroValues e16 = true := initiallyEmpty
  change (!TypedMachine.eval s zeroValues e16 ||
    ((TypedMachine.eval s zeroValues e1587 && TypedMachine.eval s zeroValues e1589) &&
      TypedMachine.eval s zeroValues e1592)) = true at before
  simp only [empty, Bool.not_true, Bool.false_or, Bool.and_eq_true] at before
  have mac : TypedMachine.eval s f e1587 = true := before.1.1
  have noExpiry : TypedMachine.eval s f e1592 = true := before.2
  cases overlap <;>
    change (((TypedMachine.eval s f e1587 && true) && TypedMachine.eval s f e1592) && true) = true <;>
    simp [mac, noExpiry]

set_option maxHeartbeats 900000 in
private theorem pending_queue (s : Snapshot) (f : Values) (overlap : Bool)
    (pending : TypedMachine.eval s f e35 = true) :
    checkedClause (rule overlap .pending) e1614 s f := by
  cases overlap <;> change (TypedMachine.eval s f e35 && true) = true <;> simp [pending]

-- Each link phase has distinct queue and timer effects, checked against the actual actions.
set_option maxHeartbeats 2200000 in
private theorem link_clauses (s : Snapshot) (f : Values) (overlap : Bool) (phase : LinkPhase)
    (valid : invariantsHold model s = true) (enabled : TypedMachine.eval s f (linkGuard phase) = true)
    (est : TypedMachine.eval s f e923 = true) (room : 1 ≤ TypedMachine.eval s f e1233) :
    Each (fun inv => checkedClause (rule overlap phase) inv s f) (affected phase) := by
  have buffer := within_buffer s f overlap phase room
  have established := established_buffer s f overlap phase est
  have window := advertised_window s f overlap phase
  have packet := packet_bound s f overlap phase
  cases phase
  · have cache := empty_cache s f overlap enabled valid
    cases overlap <;> exact ⟨rfl, cache, rfl, rfl, rfl, rfl, rfl, rfl,
      buffer, established, window, packet, rfl, trivial⟩
  · have queue := pending_queue s f overlap enabled
    cases overlap <;> exact ⟨rfl, queue, rfl, buffer, established, window, packet, rfl, trivial⟩
  · exact ⟨buffer, established, window, packet, trivial⟩

private theorem certify (overlap : Bool) (phase : LinkPhase)
    (guard : (rule overlap phase).guard = .boolAnd (dataGuard overlap) (linkGuard phase))
    (actions : (rule overlap phase).actions = prefixActions (rule overlap phase) ++ [.assign .text 56 e807])
    (untouched : (prefixActions (rule overlap phase)).all (ignoresAction (.variable .text 56)) = true)
    (catalog : model.invariants.filter (fun inv => !ignoresFiring inv (cut (rule overlap phase)) none) =
      affected phase)
    (total : ∀ s f, holds (obligationsFor (cut (rule overlap phase)) none []) s f = true) :
    FiringPreserves model (rule overlap phase) none := by
  apply preserves_after_removing_text model _ none (prefixActions (rule overlap phase)) 56
    (TypedMachine.eval initial zeroValues e807) actions untouched
  · intro s f enabled
    rw [guard] at enabled
    exact of_decide_eq_true (data_guard_facts s f overlap (both s f _ _ enabled).1).1
  · change FiringPreserves model (cut (rule overlap phase)) none
    apply preserves_touched
    intro s f valid _ enabled
    change TypedMachine.eval s f (rule overlap phase).guard = true at enabled
    rw [guard] at enabled
    obtain ⟨data, link⟩ := both s f _ _ enabled
    obtain ⟨est, room⟩ := data_guard_facts s f overlap data
    refine ⟨total s f, ?_⟩
    intro inv member seen
    apply (link_clauses s f overlap phase valid link est room).of_mem
    rw [← catalog]
    exact List.mem_filter.mpr ⟨member, by simp [seen]⟩

theorem in_order_empty : Approved.raw_261_external :=
  certify false .empty rfl rfl (by decide +kernel) rfl (fun _ _ => rfl)

theorem in_order_pending : Approved.raw_262_external :=
  certify false .pending rfl rfl (by decide +kernel) rfl (fun _ _ => rfl)

theorem in_order_resolved : Approved.raw_263_external :=
  certify false .resolved rfl rfl (by decide +kernel) rfl (fun _ _ => rfl)

theorem overlap_empty : Approved.raw_264_external :=
  certify true .empty rfl rfl (by decide +kernel) rfl (fun _ _ => rfl)

theorem overlap_pending : Approved.raw_265_external :=
  certify true .pending rfl rfl (by decide +kernel) rfl (fun _ _ => rfl)

theorem overlap_resolved : Approved.raw_266_external :=
  certify true .resolved rfl rfl (by decide +kernel) rfl (fun _ _ => rfl)

def firings : List (Rule × Option Nat) :=
  [(rule_261, none), (rule_262, none), (rule_263, none),
   (rule_264, none), (rule_265, none), (rule_266, none)]

theorem checked : Each (fun p => FiringPreserves model p.1 p.2) firings :=
  ⟨in_order_empty, in_order_pending, in_order_resolved, overlap_empty, overlap_pending,
   overlap_resolved, trivial⟩

private theorem receiveMember (index : Nat) (r : Rule)
    (selected : model.rules[index]? = some r) (external : r.event ∈ model.externalEvents) :
    (r, none) ∈ rawChecks model declaredTimers :=
  raw_external_member model declaredTimers r (List.mem_iff_getElem?.mpr ⟨index, selected⟩) external

theorem members : Each (fun p => p ∈ rawChecks model declaredTimers) firings :=
  ⟨receiveMember 261 rule_261 rfl (by decide), receiveMember 262 rule_262 rfl (by decide),
   receiveMember 263 rule_263 rfl (by decide), receiveMember 264 rule_264 rfl (by decide),
   receiveMember 265 rule_265 rfl (by decide), receiveMember 266 rule_266 rfl (by decide), trivial⟩

end TCPIPReceiveData
