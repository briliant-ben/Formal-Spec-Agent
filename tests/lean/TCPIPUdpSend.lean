import Approved
import EffectConditions
import GuardedSuffix
import TCPIPSendWire

namespace TCPIPUdpSend
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts
open EffectConditions EffectFootprint GuardedSuffix TimedObligations TCPIPSendWire
set_option maxRecDepth 16384

private def packet : Expr .octets :=
  match (obligationsFor rule_18 none [e1612]).drop 1 with
  | [.intLe (.bytesLength bytes) _] => bytes
  | _ => .literal .octets []

private theorem packet_size (s : Snapshot) (f : Values) :
    (TypedMachine.eval s f packet).length = (TypedMachine.eval s f e17).length + 28 := rfl

private def prefixActions (r : Rule) := r.actions.dropLast
private def cut (r : Rule) : Rule := {r with actions := prefixActions r}

private def working : LinkPhase → Rule
  | .empty => rule_18
  | .pending => cut rule_20
  | .resolved => cut rule_22

private def delays : LinkPhase → List (Expr .boolean)
  | .empty => [.intGe e10 e44]
  | _ => []

private def post (phase : LinkPhase) (inv : Expr .boolean) : List (Expr .boolean) :=
  (obligationsFor (working phase) none [inv]).drop (delays phase).length

private def clauses : LinkPhase → List (Expr .boolean)
  | .empty => [e1594, e1597, e1601, e1604, e1608, e1611, e1612, e1614, e1615, e1628, e1721]
  | .pending => [e1608, e1611, e1612, e1614, e1615, e1721]
  | .resolved => [e1608, e1611]

private theorem both (s : Snapshot) (f : Values) (x y : Expr .boolean)
    (enabled : TypedMachine.eval s f (.boolAnd x y) = true) :
    TypedMachine.eval s f x = true ∧ TypedMachine.eval s f y = true := by
  change (TypedMachine.eval s f x && TypedMachine.eval s f y) = true at enabled
  simpa only [Bool.and_eq_true] using enabled

set_option maxHeartbeats 1600000 in
private theorem packet_clauses (s : Snapshot) (f : Values) (phase : LinkPhase)
    (fit : TypedMachine.eval s f e124 = true) :
    holds (post phase e1608) s f = true ∧ holds (post phase e1611) s f = true := by
  let size := Int.ofNat (TypedMachine.eval s f packet).length
  let payload := Int.ofNat (TypedMachine.eval s f e17).length
  have length : size = payload + 28 := by
    change Int.ofNat (TypedMachine.eval s f packet).length = _
    rw [packet_size]
    rfl
  have fit : payload ≤ 1472 := of_decide_eq_true fit
  have limit : size ≤ 1500 := by omega
  have eq : size = 20 + (8 + payload) := by omega
  have bound : (decide (size ≤ 1500) && true) = true := by
    rw [decide_eq_true limit]
    rfl
  have header : ((decide (size = 0) || decide (size = 20 + (8 + payload))) && true) = true := by
    rw [decide_eq_true eq]
    simp
  cases phase <;> exact ⟨bound, header⟩

private def queueClause (phase : Expr .boolean) : List (Expr .boolean) :=
  let size := Expr.bytesLength packet
  let empty := Expr.equal .integer size e1
  let noneOwner := Expr.equal .text e181 e5
  let ownerCases := Expr.boolOr (.equal .text e181 e181) (.equal .text e181 e208)
  [.intLe size e244, .implies (.intGe size e44) phase, .boolOr empty (.intGe size e89),
   .boolAnd (.boolOr noneOwner ownerCases) (.equal .boolean noneOwner empty)]

set_option maxHeartbeats 1600000 in
private theorem queue_clauses (s : Snapshot) (f : Values) (phase : Expr .boolean)
    (fit : TypedMachine.eval s f e124 = true)
    (enabled : TypedMachine.eval s f phase = true) :
    Each (fun e => holds [e] s f = true) (queueClause phase) := by
  let size := Int.ofNat (TypedMachine.eval s f packet).length
  let payload := Int.ofNat (TypedMachine.eval s f e17).length
  have length : size = payload + 28 := by
    change Int.ofNat (TypedMachine.eval s f packet).length = _
    rw [packet_size]
    rfl
  have low : 0 ≤ payload := Int.natCast_nonneg _
  have fit : payload ≤ 1472 := of_decide_eq_true fit
  have min : 28 ≤ size := by omega
  have max : size ≤ 1500 := by omega
  have nonzero : size ≠ 0 := by omega
  refine ⟨?_, ?_, ?_, ?_, trivial⟩
  · change (decide (size ≤ 1500) && true) = true
    rw [decide_eq_true max]
    rfl
  · change ((!decide (1 ≤ size) || TypedMachine.eval s f phase) && true) = true
    simp [enabled]
  · change ((decide (size = 0) || decide (28 ≤ size)) && true) = true
    rw [decide_eq_true min]
    simp
  · change ((true && decide (false = decide (size = 0))) && true) = true
    simp [nonzero]

set_option maxHeartbeats 1900000 in
private theorem frame_clauses (s : Snapshot) (f : Values) (phase : LinkPhase)
    (valid : invariantsHold model s = true)
    (link : TypedMachine.eval s f (linkGuard phase) = true)
    (fit : TypedMachine.eval s f e124 = true) :
    Each (fun inv => holds (post phase inv) s f = true) (clauses phase) := by
  obtain ⟨bound, header⟩ := packet_clauses s f phase fit
  cases phase
  · have queued := queue_clauses s f (.equal .text e34 e34) fit rfl
    obtain ⟨mac, noExpiry⟩ := pending_cache_requirements s f link valid
    have cache : holds (post .empty e1597) s f = true := by
      change (((TypedMachine.eval s f e1587 && true) && TypedMachine.eval s f e1592) && true) = true
      simp [mac, noExpiry]
    exact ⟨rfl, cache, rfl, rfl, bound, header, queued.1, queued.2.1, queued.2.2.1, rfl,
      queued.2.2.2.1, trivial⟩
  · have queued := queue_clauses s f e35 fit link
    exact ⟨bound, header, queued.1, queued.2.1, queued.2.2.1, queued.2.2.2.1, trivial⟩
  · exact ⟨bound, header, trivial⟩

private theorem certify (phase : LinkPhase)
    (guard : (working phase).guard = .boolAnd (linkGuard phase) e124)
    (catalog : model.invariants.filter (fun inv => !ignoresFiring inv (working phase) none) =
      clauses phase)
    (timing : obligationsFor (working phase) none [] = delays phase) :
    FiringPreserves model (working phase) none := by
  apply preserves_touched
  intro s f valid _ enabled
  rw [guard] at enabled
  obtain ⟨link, fit⟩ := both s f _ _ enabled
  have time : holds (delays phase) s f = true := by cases phase <;> rfl
  refine ⟨timing ▸ time, ?_⟩
  intro inv member seen
  have included : inv ∈ clauses phase := by
    rw [← catalog]
    exact List.mem_filter.mpr ⟨member, by simp [seen]⟩
  have checked := (frame_clauses s f phase valid link fit).of_mem included
  rw [obligationsFor_split, timing, holds, List.all_append]
  change (holds (delays phase) s f && holds (post phase inv) s f) = true
  simp [time, checked]

private abbrev fixedText (e : Expr .text) := TypedMachine.eval initial zeroValues e

theorem send_empty : Approved.raw_18_external := certify .empty rfl rfl rfl

theorem send_pending : Approved.raw_20_external := by
  apply preserves_after_removing_text model rule_20 none (prefixActions rule_20) 25 (fixedText e34)
    rfl (by decide +kernel)
  · intro s f enabled
    exact of_decide_eq_true (both s f e35 e124 enabled).1
  · exact certify .pending rfl rfl rfl

theorem send_resolved : Approved.raw_22_external := by
  apply preserves_after_removing_text model rule_22 none (prefixActions rule_22) 25 (fixedText e37)
    rfl (by decide +kernel)
  · intro s f enabled
    exact of_decide_eq_true (both s f e38 e124 enabled).1
  · exact certify .resolved rfl rfl rfl

def firings : List (Rule × Option Nat) := [(rule_18, none), (rule_20, none), (rule_22, none)]

theorem checked : Each (fun p => FiringPreserves model p.1 p.2) firings :=
  ⟨send_empty, send_pending, send_resolved, trivial⟩

private theorem sendMember (index : Nat) (r : Rule)
    (selected : model.rules[index]? = some r) (external : r.event ∈ model.externalEvents) :
    (r, none) ∈ rawChecks model declaredTimers :=
  raw_external_member model declaredTimers r (List.mem_iff_getElem?.mpr ⟨index, selected⟩) external

theorem members : Each (fun p => p ∈ rawChecks model declaredTimers) firings :=
  ⟨sendMember 18 rule_18 rfl (by decide), sendMember 20 rule_20 rfl (by decide),
   sendMember 22 rule_22 rfl (by decide), trivial⟩

end TCPIPUdpSend
