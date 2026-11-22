import Approved
import EffectConditions
import TimedObligations

namespace TCPIPUDPDeliver
open Approved FormalSpecAgent FormalSpecAgent.TypedIR FormalSpecAgent.TypedMachine
open EffectConditions EffectFootprint TypedFiringContracts TimedObligations

private theorem andParts (s : Snapshot) (f : Values) (a b : Expr .boolean)
    (both : TypedMachine.eval s f (.boolAnd a b) = true) :
    TypedMachine.eval s f a = true ∧ TypedMachine.eval s f b = true := by
  change (TypedMachine.eval s f a && TypedMachine.eval s f b) = true at both
  simpa only [Bool.and_eq_true] using both

private theorem payload_bound (s : Snapshot) (f : Values)
    (guard : TypedMachine.eval s f e339 = true) :
    (Int.ofNat (TypedMachine.eval s f e342).length) ≤ 1472 := by
  have envelope := (andParts s f e253 e338 guard).2
  have sizes := andParts s f e285 e304 (andParts s f e305 e337 envelope).1
  have lengthEquality := (andParts s f e302 e303 sizes.2).2
  have ip5 := (andParts s f e276 e279 sizes.1).1
  have ip4 := (andParts s f e269 e275 ip5).1
  have ip3 := (andParts s f e265 e268 ip4).1
  have ip2 := (andParts s f e261 e264 ip3).1
  have ip1 := (andParts s f e258 e260 ip2).1
  have bound : TypedMachine.eval s f e255 ≤ 1500 :=
    of_decide_eq_true (andParts s f e256 e257 ip1).2
  have same : TypedMachine.eval s f e291 = TypedMachine.eval s f e255 - 20 :=
    of_decide_eq_true lengthEquality
  have cap (data : Bytes) (start count : Int) :
      (Int.ofNat (byteSlice data start count).length) ≤ Int.ofNat count.toNat := by
    unfold byteSlice
    exact Int.ofNat_le.mpr (List.length_take_le ..)
  have clipped := cap (TypedMachine.eval s f e254) 28 (TypedMachine.eval s f e291 - 8)
  change (Int.ofNat (byteSlice (TypedMachine.eval s f e254) 28 (TypedMachine.eval s f e291 - 8)).length)
    ≤ 1472
  have clipLimit (ipLength : Int) (upper : ipLength ≤ 1500) :
      (Int.ofNat (ipLength - 20 - 8).toNat) ≤ 1472 := by
    change ((ipLength - 20 - 8).toNat : Int) ≤ 1472
    omega
  rw [same] at clipped ⊢
  exact Int.le_trans clipped (clipLimit _ bound)

private def affected := [e1594, e1597, e1601, e1614, e1617, e1621, e1628]

private theorem discharge (rule : Rule) (s : Snapshot) (f : Values)
    (catalog : model.invariants.filter (fun inv => !ignoresFiring inv rule none) = affected)
    (checked : Each (fun inv => holds (obligationsFor rule none [inv]) s f = true) affected) :
    ∀ inv ∈ model.invariants, ignoresFiring inv rule none = false →
      holds (obligationsFor rule none [inv]) s f = true := by
  intro inv member observed
  apply checked.of_mem
  rw [← catalog]
  exact List.mem_filter.mpr ⟨member, by simp [observed]⟩

private theorem from_phase (s : Snapshot) (phase requirement : Expr .boolean)
    (valid : invariantsHold model s = true) (member : (.implies phase requirement) ∈ model.invariants)
    (matching : TypedMachine.eval s zeroValues phase = true) :
    TypedMachine.eval s zeroValues requirement = true := by
  have current := List.all_eq_true.mp valid (.implies phase requirement) member
  change ((!TypedMachine.eval s zeroValues phase) || TypedMachine.eval s zeroValues requirement) = true
    at current
  simpa only [matching, Bool.not_true, Bool.false_or] using current

private theorem not_queued (s : Snapshot) (valid : invariantsHold model s = true)
    (notPending : TypedMachine.eval s zeroValues e35 = false) :
    TypedMachine.eval s zeroValues e1613 = false := by
  have checked := List.all_eq_true.mp valid e1614 (by rw [model_invariants]; simp)
  change (!TypedMachine.eval s zeroValues e1613 || TypedMachine.eval s zeroValues e35) = true at checked
  rw [notPending, Bool.or_false] at checked
  exact Bool.not_eq_true' _ ▸ checked

private theorem bounded_output (s : Snapshot) (f : Values) (bound : TypedMachine.eval s f e339 = true) :
    (decide ((Int.ofNat (TypedMachine.eval s f e342).length) ≤ 1472) && true) = true := by
  rw [decide_eq_true (payload_bound s f bound)]
  rfl

theorem deliver_empty : Approved.raw_35_external := by
  apply preserves_touched
  intro s f valid _ enabled
  obtain ⟨phase, envelope⟩ := andParts s f e16 e339 enabled
  have prior : TypedMachine.eval s f e1593 = true :=
    from_phase s e16 e1593 valid (by change e1594 ∈ _; rw [model_invariants]; simp) phase
  have state : TypedMachine.eval s zeroValues e15 = TypedMachine.eval s zeroValues e6 :=
    of_decide_eq_true phase
  have nonpending : TypedMachine.eval s zeroValues e35 = false := by
    change decide (TypedMachine.eval s zeroValues e15 = TypedMachine.eval s zeroValues e34) = false
    rw [state]
    rfl
  have empty : TypedMachine.eval s f e1613 = false := not_queued s valid nonpending
  refine ⟨rfl, discharge _ s f rfl ?_⟩
  refine ⟨?_, rfl, rfl, ?_, ?_, rfl, rfl, trivial⟩
  · change (TypedMachine.eval s f e1593 && true) = true
    simp [prior]
  · change ((!TypedMachine.eval s f e1613 || false) && true) = true
    simp [empty]
  · exact bounded_output s f envelope

theorem deliver_pending : Approved.raw_42_external := by
  apply preserves_touched
  intro s f valid _ enabled
  obtain ⟨phase, envelope⟩ := andParts s f e35 e339 enabled
  have prior : TypedMachine.eval s f e1596 = true :=
    from_phase s e35 e1596 valid (by change e1597 ∈ _; rw [model_invariants]; simp) phase
  refine ⟨rfl, discharge _ s f rfl ?_⟩
  refine ⟨rfl, ?_, rfl, ?_, ?_, rfl, rfl, trivial⟩
  · change (TypedMachine.eval s f e1596 && true) = true
    simp [prior]
  · change ((!TypedMachine.eval s f e1613 || true) && true) = true
    simp
  · exact bounded_output s f envelope

theorem deliver_resolved : Approved.raw_49_external := by
  apply preserves_touched
  intro s f valid _ enabled
  obtain ⟨phase, envelope⟩ := andParts s f e38 e339 enabled
  have prior : TypedMachine.eval s f e1600 = true :=
    from_phase s e38 e1600 valid (by change e1601 ∈ _; rw [model_invariants]; simp) phase
  have state : TypedMachine.eval s zeroValues e15 = TypedMachine.eval s zeroValues e37 :=
    of_decide_eq_true phase
  have nonpending : TypedMachine.eval s zeroValues e35 = false := by
    change decide (TypedMachine.eval s zeroValues e15 = TypedMachine.eval s zeroValues e34) = false
    rw [state]
    rfl
  have empty : TypedMachine.eval s f e1613 = false := not_queued s valid nonpending
  refine ⟨rfl, discharge _ s f rfl ?_⟩
  refine ⟨rfl, rfl, ?_, ?_, ?_, rfl, rfl, trivial⟩
  · change (TypedMachine.eval s f e1600 && true) = true
    simp [prior]
  · change ((!TypedMachine.eval s f e1613 || false) && true) = true
    simp [empty]
  · exact bounded_output s f envelope

def firings : List (Rule × Option Nat) := [(rule_35, none), (rule_42, none), (rule_49, none)]

theorem checked : Each (fun p => FiringPreserves model p.1 p.2) firings :=
  ⟨deliver_empty, deliver_pending, deliver_resolved, trivial⟩

private theorem deliveryMember (index : Nat) (rule : Rule)
    (selected : model.rules[index]? = some rule) (external : rule.event ∈ model.externalEvents) :
    (rule, none) ∈ rawChecks model declaredTimers :=
  raw_external_member model declaredTimers rule (List.mem_iff_getElem?.mpr ⟨index, selected⟩) external

theorem members : Each (fun p => p ∈ rawChecks model declaredTimers) firings :=
  ⟨deliveryMember 35 rule_35 rfl (by decide), deliveryMember 42 rule_42 rfl (by decide),
    deliveryMember 49 rule_49 rfl (by decide), trivial⟩

end TCPIPUDPDeliver
