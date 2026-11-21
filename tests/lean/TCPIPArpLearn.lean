import Approved
import EffectConditions

namespace TCPIPArpLearn
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts
open EffectConditions EffectFootprint TimedObligations

private theorem both (s : Snapshot) (f : Values) (x y : Expr .boolean)
    (enabled : TypedMachine.eval s f (.boolAnd x y) = true) :
    TypedMachine.eval s f x = true ∧ TypedMachine.eval s f y = true := by
  change (TypedMachine.eval s f x && TypedMachine.eval s f y) = true at enabled
  simpa only [Bool.and_eq_true] using enabled

private def operation (request : Bool) : Expr .boolean := if request then e98 else e110

private theorem frame_minimum (s : Snapshot) (f : Values)
    (header : TypedMachine.eval s f e93 = true) : 42 ≤ TypedMachine.eval s f e52 := by
  have address := (both s f e88 e92 header).1
  have consistent := (both s f e85 e87 address).1
  have base := (both s f e80 e84 consistent).1
  have typ := (both s f e71 e79 base).1
  have size := (both s f e66 e70 typ).1
  have limits := (both s f e60 e65 size).1
  exact of_decide_eq_true (both s f e57 e59 limits).1

private theorem local_header (s : Snapshot) (f : Values) (request : Bool)
    (ok : TypedMachine.eval s f (operation request) = true) : TypedMachine.eval s f e93 = true := by
  cases request
  · exact (both s f e93 e96 (both s f e97 e109 ok).1).1
  · exact (both s f e93 e96 (both s f e97 e76 ok).1).1

private theorem mac_length (s : Snapshot) (f : Values) (min : 42 ≤ TypedMachine.eval s f e52) :
    Int.ofNat (TypedMachine.eval s f e83).length = 6 := by
  let frame := TypedMachine.eval s f e17
  have enough : 42 ≤ (frame.length : Int) := min
  have suffix : 6 ≤ (frame.drop 22).length := by
    rw [List.length_drop]
    omega
  change Int.ofNat ((frame.drop 22).take 6).length = 6
  rw [List.length_take, Nat.min_eq_left suffix]
  rfl

private theorem no_queue_outside_pending (s : Snapshot) (f : Values)
    (notPending : TypedMachine.eval s f e35 = false)
    (valid : invariantsHold model s = true) : TypedMachine.eval s f e1613 = false := by
  have queued : TypedMachine.eval s f e1614 = true :=
    List.all_eq_true.mp valid e1614 (by rw [model_invariants]; simp)
  change (!TypedMachine.eval s f e1613 || TypedMachine.eval s f e35) = true at queued
  rw [notPending, Bool.or_false] at queued
  exact Bool.not_eq_true' _ ▸ queued

private theorem resolved_no_query (s : Snapshot) (f : Values)
    (resolved : TypedMachine.eval s f e38 = true)
    (valid : invariantsHold model s = true) : TypedMachine.eval s f e1589 = true := by
  have inv : TypedMachine.eval s f e1601 = true :=
    List.all_eq_true.mp valid e1601 (by rw [model_invariants]; simp)
  change (!TypedMachine.eval s f e38 || ((TypedMachine.eval s f e1598 &&
    TypedMachine.eval s f e1589) && TypedMachine.eval s f e1591)) = true at inv
  simp only [resolved, Bool.not_true, Bool.false_or, Bool.and_eq_true] at inv
  exact inv.1.2

private def reads (cancelQuery clearQueue : Bool) : ExprRewrite.Rewrite :=
  { varRead := fun kind slot =>
      match kind with
      | .text => if slot = 25 then e37 else if slot = 57 && clearQueue then e5 else .variable .text slot
      | .octets => if slot = 0 then e83 else if slot = 16 && clearQueue then e0 else .variable .octets slot
      | .integer => if slot = 1 && cancelQuery then e1 else .variable .integer slot
      | .boolean => .variable .boolean slot
      | .sequence => .variable .sequence slot
    field := fun kind slot => .literal kind (getValue kind zeroValues slot)
    stateIs := fun id => .literal .boolean (decide (0 = id))
    timerActive := fun id =>
      if id = 0 then .literal .boolean true else
      if id = 1 && cancelQuery then .literal .boolean false else .timerActive id }

private def checks (cancelQuery clearQueue : Bool) : List (Expr .boolean) :=
  [e1594, e1597, e1601] ++ (if cancelQuery then [e1604] else []) ++
    (if clearQueue then [e1612, e1614, e1615, e1628, e1721] else [e1614, e1628])

private theorem checked_clauses (s : Snapshot) (f : Values) (cancelQuery clearQueue : Bool)
    (mac : Int.ofNat (TypedMachine.eval s f e83).length = 6)
    (queryOff : cancelQuery = false → TypedMachine.eval s f e1589 = true)
    (noQueue : clearQueue = false → TypedMachine.eval s f e1613 = false) :
    Each (fun inv => TypedMachine.eval s f (ExprRewrite.run (reads cancelQuery clearQueue) inv) = true)
      (checks cancelQuery clearQueue) := by
  have cache : TypedMachine.eval s f (ExprRewrite.run (reads cancelQuery clearQueue) e1601) = true := by
    cases clearQueue <;> cases cancelQuery
    all_goals first
    | (change ((decide (Int.ofNat (TypedMachine.eval s f e83).length = 6) &&
         TypedMachine.eval s f e1589) && true) = true
       rw [mac, queryOff rfl]; rfl)
    | (change ((decide (Int.ofNat (TypedMachine.eval s f e83).length = 6) && true) && true) = true
       rw [mac]; rfl)
  have queued : TypedMachine.eval s f (ExprRewrite.run (reads cancelQuery clearQueue) e1614) = true := by
    cases clearQueue
    · change (!TypedMachine.eval s f e1613 || false) = true
      rw [noQueue rfl]
      rfl
    · rfl
  cases clearQueue <;> cases cancelQuery
  · exact ⟨rfl, rfl, cache, queued, rfl, trivial⟩
  · exact ⟨rfl, rfl, cache, rfl, queued, rfl, trivial⟩
  · exact ⟨rfl, rfl, cache, rfl, queued, rfl, rfl, rfl, trivial⟩
  · exact ⟨rfl, rfl, cache, rfl, rfl, queued, rfl, rfl, rfl, trivial⟩

private theorem learn (r : Rule) (cancelQuery clearQueue : Bool)
    (catalog : model.invariants.filter (fun inv => !ignoresFiring inv r none) = checks cancelQuery clearQueue)
    (timing : obligationsFor r none [] = [.intGe e100 e44])
    (align : (checks cancelQuery clearQueue).map (fun inv => (obligationsFor r none [inv]).drop 1)
      = (checks cancelQuery clearQueue).map (fun inv => [ExprRewrite.run (reads cancelQuery clearQueue) inv]))
    (facts : ∀ s f, invariantsHold model s = true → TypedMachine.eval s f r.guard = true →
      42 ≤ TypedMachine.eval s f e52 ∧
      (cancelQuery = false → TypedMachine.eval s f e1589 = true) ∧
      (clearQueue = false → TypedMachine.eval s f e1613 = false)) :
    FiringPreserves model r none := by
  apply preserves_touched
  intro s f valid _ enabled
  obtain ⟨len, query, queue⟩ := facts s f valid enabled
  have ttl : TypedMachine.eval s f e1607 = true :=
    List.all_eq_true.mp valid e1607 (by rw [model_invariants]; simp)
  obtain ⟨ttlMin, _⟩ := both s f e1605 e1606 ttl
  have minimum : 60000 ≤ TypedMachine.eval s f e100 := of_decide_eq_true ttlMin
  have delay : holds [.intGe e100 e44] s f = true := by
    change (decide (1 ≤ TypedMachine.eval s f e100) && true) = true
    rw [decide_eq_true (Int.le_trans (by decide : (1 : Int) ≤ 60000) minimum)]
    rfl
  refine ⟨timing ▸ delay, ?_⟩
  intro inv member seen
  have found : inv ∈ checks cancelQuery clearQueue := by
    rw [← catalog]
    exact List.mem_filter.mpr ⟨member, by simp [seen]⟩
  have post := (checked_clauses s f cancelQuery clearQueue (mac_length s f len) query queue).of_mem found
  rw [obligationsFor_split, timing, holds, List.all_append]
  change (holds [.intGe e100 e44] s f &&
    holds ((obligationsFor r none [inv]).drop 1) s f) = true
  rw [List.map_inj_left.mp align inv found]
  change (holds [.intGe e100 e44] s f &&
    (TypedMachine.eval s f (ExprRewrite.run (reads cancelQuery clearQueue) inv) && true)) = true
  simp [delay, post]

private abbrev fixedText (e : Expr .text) := TypedMachine.eval initial zeroValues e

private theorem outside_pending (s : Snapshot) (f : Values) (phase : String)
    (distinct : phase ≠ fixedText e34)
    (enabled : TypedMachine.eval s f (.equal .text e15 (.literal .text phase)) = true)
    (valid : invariantsHold model s = true) : TypedMachine.eval s f e1613 = false := by
  have state : TypedMachine.eval s f e15 = phase := of_decide_eq_true enabled
  apply no_queue_outside_pending s f _ valid
  change decide (TypedMachine.eval s f e15 = fixedText e34) = false
  rw [state]
  exact decide_eq_false distinct

private theorem ordinary (r : Rule) (phase : String) (request : Bool)
    (distinct : phase ≠ fixedText e34)
    (shape : r.guard = .boolAnd (.equal .text e15 (.literal .text phase)) (operation request))
    (catalog : model.invariants.filter (fun inv => !ignoresFiring inv r none) = checks true false)
    (timing : obligationsFor r none [] = [.intGe e100 e44])
    (align : (checks true false).map (fun inv => (obligationsFor r none [inv]).drop 1)
      = (checks true false).map (fun inv => [ExprRewrite.run (reads true false) inv])) :
    FiringPreserves model r none := by
  apply learn r true false catalog timing align
  intro s f valid enabled
  rw [shape] at enabled
  obtain ⟨link, packet⟩ := both s f _ _ enabled
  exact ⟨frame_minimum s f (local_header s f request packet), (by intro h; cases h),
    fun _ => outside_pending s f phase distinct link valid⟩

private theorem pending (r : Rule) (request clearQueue : Bool)
    (shape : r.guard = .boolAnd e35 (.boolAnd (operation request) (if clearQueue then e201 else e211)))
    (catalog : model.invariants.filter (fun inv => !ignoresFiring inv r none) = checks true clearQueue)
    (timing : obligationsFor r none [] = [.intGe e100 e44])
    (align : (checks true clearQueue).map (fun inv => (obligationsFor r none [inv]).drop 1)
      = (checks true clearQueue).map (fun inv => [ExprRewrite.run (reads true clearQueue) inv])) :
    FiringPreserves model r none := by
  apply learn r true clearQueue catalog timing align
  intro s f _ enabled
  rw [shape] at enabled
  obtain ⟨packet, queue⟩ := both s f _ _ (both s f _ _ enabled).2
  refine ⟨frame_minimum s f (local_header s f request packet), (by intro h; cases h), ?_⟩
  intro empty
  cases empty
  have zero : TypedMachine.eval s f e200 = 0 := of_decide_eq_true queue
  change decide (1 ≤ TypedMachine.eval s f e200) = false
  rw [zero]
  rfl

theorem local_request_empty : Approved.raw_7_external :=
  ordinary rule_7 (fixedText e6) true (by decide) rfl rfl rfl rfl

theorem local_reply_empty : Approved.raw_8_external :=
  ordinary rule_8 (fixedText e6) false (by decide) rfl rfl rfl rfl

theorem local_request_resolved : Approved.raw_15_external :=
  ordinary rule_15 (fixedText e37) true (by decide) rfl rfl rfl rfl

theorem local_reply_resolved : Approved.raw_16_external :=
  ordinary rule_16 (fixedText e37) false (by decide) rfl rfl rfl rfl

theorem nonlocal_resolved : Approved.raw_17_external := by
  apply learn rule_17 false false rfl rfl rfl
  intro s f valid enabled
  obtain ⟨resolved, packet⟩ := both s f e38 e113 enabled
  exact ⟨frame_minimum s f (both s f e93 e112 packet).1,
    fun _ => resolved_no_query s f resolved valid,
    fun _ => outside_pending s f (fixedText e37) (by decide) resolved valid⟩

theorem local_request_queued : Approved.raw_27_external :=
  pending rule_27 true true rfl rfl rfl rfl

theorem local_request_unqueued : Approved.raw_28_external :=
  pending rule_28 true false rfl rfl rfl rfl

theorem local_reply_queued : Approved.raw_29_external :=
  pending rule_29 false true rfl rfl rfl rfl

theorem local_reply_unqueued : Approved.raw_30_external :=
  pending rule_30 false false rfl rfl rfl rfl

def firings : List (Rule × Option Nat) :=
  [(rule_7, none), (rule_8, none), (rule_15, none), (rule_16, none), (rule_17, none),
   (rule_27, none), (rule_28, none), (rule_29, none), (rule_30, none)]

theorem checked : Each (fun p => FiringPreserves model p.1 p.2) firings :=
  ⟨local_request_empty, local_reply_empty, local_request_resolved, local_reply_resolved,
   nonlocal_resolved, local_request_queued, local_request_unqueued, local_reply_queued,
   local_reply_unqueued, trivial⟩

private theorem learnMember (index : Nat) (r : Rule)
    (selected : model.rules[index]? = some r) (external : r.event ∈ model.externalEvents) :
    (r, none) ∈ rawChecks model declaredTimers :=
  raw_external_member model declaredTimers r (List.mem_iff_getElem?.mpr ⟨index, selected⟩) external

theorem members : Each (fun p => p ∈ rawChecks model declaredTimers) firings :=
  ⟨learnMember 7 rule_7 rfl (by decide), learnMember 8 rule_8 rfl (by decide),
   learnMember 15 rule_15 rfl (by decide), learnMember 16 rule_16 rfl (by decide),
   learnMember 17 rule_17 rfl (by decide), learnMember 27 rule_27 rfl (by decide),
   learnMember 28 rule_28 rfl (by decide), learnMember 29 rule_29 rfl (by decide),
   learnMember 30 rule_30 rfl (by decide), trivial⟩

end TCPIPArpLearn
