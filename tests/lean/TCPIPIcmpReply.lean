import Approved
import EffectConditions
import GuardedSuffix

namespace TCPIPIcmpReply
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts
open EffectConditions EffectFootprint GuardedSuffix TimedObligations
set_option maxRecDepth 16384

private theorem both (s : Snapshot) (f : Values) (x y : Expr .boolean)
    (enabled : TypedMachine.eval s f (.boolAnd x y) = true) :
    TypedMachine.eval s f x = true ∧ TypedMachine.eval s f y = true := by
  change (TypedMachine.eval s f x && TypedMachine.eval s f y) = true at enabled
  simpa only [Bool.and_eq_true] using enabled

private theorem packet_limits (s : Snapshot) (f : Values)
    (enabled : TypedMachine.eval s f e432 = true) :
    28 ≤ TypedMachine.eval s f e255 ∧ TypedMachine.eval s f e255 ≤ 1500 := by
  have typeAndChecksum := (both s f e253 e431 enabled).2
  have checks := (both s f e422 e425 typeAndChecksum).1
  have header := (both s f e418 e279 checks).1
  have addresses := (both s f e417 e275 header).1
  have target := (both s f e414 e416 addresses).1
  have source := (both s f e411 e413 target).1
  have ttl := (both s f e408 e410 source).1
  have code := (both s f e404 e407 ttl).1
  have kind := (both s f e401 e403 code).1
  have protocol := (both s f e397 e400 kind).1
  have fragment := (both s f e394 e396 protocol).1
  have flags := (both s f e390 e393 fragment).1
  have headerFormat := (both s f e387 e389 flags).1
  have length := (both s f e258 e386 headerFormat).1
  exact ⟨of_decide_eq_true (both s f e256 e257 length).1,
    of_decide_eq_true (both s f e256 e257 length).2⟩

private theorem slice_bound (bytes : Bytes) (offset count : Int) :
    (byteSlice bytes offset count).length ≤ count.toNat := by
  rw [byteSlice, List.length_take]
  exact Nat.min_le_left ..

private theorem reply_size (ip icmp : Bytes) (ipChecksum icmpChecksum count : Int)
    (valid : 0 ≤ count) (fits : count ≤ 1476) :
    Int.ofNat (((byteSlice ip 0 10 ++ ValueOps.pack16 ipChecksum) ++ byteSlice ip 12 8) ++
      (([0, 0] ++ ValueOps.pack16 icmpChecksum) ++ byteSlice icmp 4 count)).length ≤ 1500 := by
  have ipFirst := slice_bound ip 0 10
  have ipLast := slice_bound ip 12 8
  have data := slice_bound icmp 4 count
  simp only [List.length_append, ValueOps.pack16, List.length_cons, List.length_nil]
  apply Int.ofNat_le.mpr
  change ((byteSlice ip 0 10).length + 2 + (byteSlice ip 12 8).length) +
    (4 + (byteSlice icmp 4 count).length) ≤ 1500
  have a : (byteSlice ip 0 10).length ≤ 10 := ipFirst
  have b : (byteSlice ip 12 8).length ≤ 8 := ipLast
  omega

private def prefixActions (r : Rule) := r.actions.dropLast
private def cut (r : Rule) : Rule := {r with actions := prefixActions r}

private theorem certify (r : Rule) (phase : String)
    (shape : r.guard = .boolAnd (.equal .text e15 (.literal .text phase)) e432)
    (actions : r.actions = prefixActions r ++ [.assign .text 25 (.literal .text phase)])
    (untouched : (prefixActions r).all (ignoresAction (.variable .text 25)) = true)
    (catalog : model.invariants.filter (fun inv => !ignoresFiring inv (cut r) none) =
      [e1622, e1626])
    (total : obligationsFor (cut r) none [] = [])
    (bound : ∀ s f, TypedMachine.eval s f e432 = true →
      holds (obligationsFor (cut r) none [e1622]) s f = true)
    (kind : ∀ s f, holds (obligationsFor (cut r) none [e1626]) s f = true) :
    FiringPreserves model r none := by
  apply preserves_after_removing_text model r none (prefixActions r) 25 phase actions untouched
  · intro s f enabled
    rw [shape] at enabled
    exact of_decide_eq_true (both s f _ _ enabled).1
  · change FiringPreserves model (cut r) none
    apply preserves_touched
    intro s f _ _ enabled
    change TypedMachine.eval s f r.guard = true at enabled
    rw [shape] at enabled
    refine ⟨total.symm ▸ rfl, ?_⟩
    intro inv member seen
    have found : inv ∈ [e1622, e1626] := by
      rw [← catalog]
      exact List.mem_filter.mpr ⟨member, by simp [seen]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at found
    rcases found with rfl | rfl
    · exact bound s f (both s f _ _ enabled).2
    · exact kind s f

private theorem reply (s : Snapshot) (f : Values)
    (checked : TypedMachine.eval s f e432 = true) :
    holds (obligationsFor (cut rule_54) none [e1622]) s f = true := by
  obtain ⟨minimum, maximum⟩ := packet_limits s f checked
  let count := TypedMachine.eval s f e435
  have bounds (len : Int) (low : 28 ≤ len) (high : len ≤ 1500) :
      0 ≤ len - 24 ∧ len - 24 ≤ 1476 := by omega
  have fits : 0 ≤ count ∧ count ≤ 1476 := bounds _ minimum maximum
  change (decide (Int.ofNat (((byteSlice _ 0 10 ++ ValueOps.pack16 _) ++ byteSlice _ 12 8) ++
      (([0, 0] ++ ValueOps.pack16 _) ++ byteSlice _ 4 count)).length ≤ 1500) && true) = true
  rw [decide_eq_true (reply_size _ _ _ _ count fits.1 fits.2)]
  rfl

private abbrev fixedText (e : Expr .text) := TypedMachine.eval initial zeroValues e

theorem echo_empty : Approved.raw_54_external :=
  certify rule_54 (fixedText e6) rfl rfl (by decide +kernel) rfl rfl reply (fun _ _ => rfl)

theorem echo_pending : Approved.raw_58_external :=
  certify rule_58 (fixedText e34) rfl rfl (by decide +kernel) rfl rfl reply (fun _ _ => rfl)

theorem echo_resolved : Approved.raw_62_external :=
  certify rule_62 (fixedText e37) rfl rfl (by decide +kernel) rfl rfl reply (fun _ _ => rfl)

def firings : List (Rule × Option Nat) := [(rule_54, none), (rule_58, none), (rule_62, none)]

theorem checked : Each (fun p => FiringPreserves model p.1 p.2) firings :=
  ⟨echo_empty, echo_pending, echo_resolved, trivial⟩

private theorem replyMember (index : Nat) (r : Rule)
    (selected : model.rules[index]? = some r) (external : r.event ∈ model.externalEvents) :
    (r, none) ∈ rawChecks model declaredTimers :=
  raw_external_member model declaredTimers r (List.mem_iff_getElem?.mpr ⟨index, selected⟩) external

theorem members : Each (fun p => p ∈ rawChecks model declaredTimers) firings :=
  ⟨replyMember 54 rule_54 rfl (by decide), replyMember 58 rule_58 rfl (by decide),
   replyMember 62 rule_62 rfl (by decide), trivial⟩

end TCPIPIcmpReply
