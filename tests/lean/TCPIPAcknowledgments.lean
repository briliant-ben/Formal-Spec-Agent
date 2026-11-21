import Approved
import EffectConditions
import GuardedSuffix
import SequenceFacts
import OctetFacts

namespace TCPIPAcknowledgments
open Approved FormalSpecAgent TypedIR TypedMachine TypedContracts TypedFiringContracts
open EffectConditions EffectFootprint GuardedSuffix TimedObligations

private theorem octet_range (data : Bytes) (offset : Int) :
    0 ≤ byteAt data offset ∧ byteAt data offset ≤ 255 := by
  unfold byteAt
  split
  · decide
  · have finite := (data.getD offset.toNat 0).isLt
    change 0 ≤ ((data.getD offset.toNat 0).val : Int) ∧
      ((data.getD offset.toNat 0).val : Int) ≤ 255
    omega

private theorem advertised_range (s : Snapshot) (f : Values) :
    0 ≤ TypedMachine.eval s f e772 ∧ TypedMachine.eval s f e772 ≤ 65535 := by
  have combine (hi lo : Int) (h : 0 ≤ hi ∧ hi ≤ 255) (l : 0 ≤ lo ∧ lo ≤ 255) :
      0 ≤ hi * 256 + lo ∧ hi * 256 + lo ≤ 65535 := by
    omega
  exact combine _ _ (octet_range (TypedMachine.eval s f e583) 34)
    (octet_range (TypedMachine.eval s f e583) 35)

private theorem parts (s : Snapshot) (f : Values) (x y : Expr .boolean)
    (enabled : TypedMachine.eval s f (.boolAnd x y) = true) :
    TypedMachine.eval s f x = true ∧ TypedMachine.eval s f y = true := by
  change (TypedMachine.eval s f x && TypedMachine.eval s f y) = true at enabled
  simpa only [Bool.and_eq_true] using enabled

private theorem guard_facts (s : Snapshot) (f : Values)
    (enabled : TypedMachine.eval s f rule_252.guard = true) :
    TypedMachine.eval s f e923 = true ∧ TypedMachine.eval s f e929 ≤ TypedMachine.eval s f e772 := by
  have first := (parts s f e1305 e721 enabled).1
  have splitGuard := parts s f e923 e1304 first
  have updates := (parts s f e812 e1303 splitGuard.2).2
  have current := (parts s f e1302 e1278 updates).1
  exact ⟨splitGuard.1, of_decide_eq_true (parts s f e1300 e1301 current).2⟩

private abbrev estimate (s : Snapshot) (f : Values) := TypedMachine.eval s f e1259
private abbrev outstanding (s : Snapshot) (f : Values) := TypedMachine.eval s f e929
private abbrev leftLength (s : Snapshot) (f : Values) := Int.ofNat (TypedMachine.eval s f e1283).length

private theorem projectedLength (s : Snapshot) (f : Values)
    (lower : 1 ≤ estimate s f) (upper : estimate s f ≤ outstanding s f) :
    leftLength s f = outstanding s f - estimate s f :=
  OctetFacts.suffix_length (TypedMachine.eval s f e928) (estimate s f)
    (Int.le_trans (by decide : (0 : Int) ≤ 1) lower) upper

private theorem prefix_trims_sequence (s : Snapshot) (f : Values)
    (valid : invariantsHold model s = true) (phase : TypedMachine.eval s f e923 = true)
    (remaining : leftLength s f = outstanding s f - estimate s f) :
    TypedMachine.eval s f e763 =
      ValueOps.seqAdd (TypedMachine.eval s f e762) (leftLength s f) := by
  have old := List.all_eq_true.mp valid e1690 (by rw [model_invariants]; simp)
  have established : TypedMachine.eval s zeroValues e923 = true := phase
  change (!TypedMachine.eval s zeroValues e923 || TypedMachine.eval s zeroValues e1689) = true at old
  simp only [established, Bool.not_true, Bool.false_or] at old
  have oldSeq : TypedMachine.eval s f e763 =
      ValueOps.seqAdd (TypedMachine.eval s f e976) (outstanding s f) :=
    of_decide_eq_true old
  have acknowledgment :
      ValueOps.seqAdd (TypedMachine.eval s f e976) (estimate s f) = TypedMachine.eval s f e762 :=
    SequenceFacts.add_distance _ _
  have sum (count n : Int) : n + (count - n) = count := by omega
  rw [← acknowledgment, remaining, SequenceFacts.add_add, sum]
  exact oldSeq

private structure DataFacts (s : Snapshot) (f : Values) where
  ordered : TypedMachine.eval s f e923 = true
  sameSequence : TypedMachine.eval s f e763 =
    ValueOps.seqAdd (TypedMachine.eval s f e762) (leftLength s f)
  sendBound : TypedMachine.eval s f e925 + leftLength s f ≤ 16
  freshBound : leftLength s f ≤ TypedMachine.eval s f e772
  staleBound : leftLength s f ≤ TypedMachine.eval s f e1221
  positiveDelay : 1 ≤ TypedMachine.eval s f e566

private theorem data_facts (s : Snapshot) (f : Values)
    (valid : invariantsHold model s = true) (phase : TypedMachine.eval s f e923 = true)
    (lower : 1 ≤ estimate s f) (upper : estimate s f ≤ outstanding s f)
    (peer : outstanding s f - estimate s f ≤ TypedMachine.eval s f e772) :
    DataFacts s f := by
  have rest := projectedLength s f lower upper
  have monotone (old n : Int) (positive : 1 ≤ n) : old - n ≤ old := by omega
  have notGreater : leftLength s f ≤ outstanding s f :=
    rest ▸ monotone _ _ lower
  have sendClause := List.all_eq_true.mp valid e1691 (by rw [model_invariants]; simp)
  have sendBound : TypedMachine.eval s f e925 + outstanding s f ≤ 16 :=
    of_decide_eq_true sendClause
  have windowClause := List.all_eq_true.mp valid e1705 (by rw [model_invariants]; simp)
  have current : outstanding s f ≤ TypedMachine.eval s f e1221 := of_decide_eq_true windowClause
  have retryClause := List.all_eq_true.mp valid e1680 (by rw [model_invariants]; simp)
  have delay : 1000 ≤ TypedMachine.eval s f e566 := of_decide_eq_true retryClause
  exact ⟨phase, prefix_trims_sequence s f valid phase rest,
    Int.le_trans (Int.add_le_add_left notGreater _) sendBound, rest ▸ peer,
    Int.le_trans notGreater current, Int.le_trans (by decide : (1 : Int) ≤ 1000) delay⟩

private def prefixActions (rule : Rule) := rule.actions.dropLast

private def shorten (rule : Rule) : Rule := { rule with actions := prefixActions rule }

private theorem certify (rule : Rule)
    (actions : rule.actions = prefixActions rule ++ [.assign .text 56 e807])
    (untouched : (prefixActions rule).all (ignoresAction (.variable .text 56)) = true)
    (phase : ∀ s f, TypedMachine.eval s f rule.guard = true → TypedMachine.eval s f e923 = true)
    (catalog : model.invariants.filter (fun inv => !ignoresFiring inv (shorten rule) none) = affected)
    (proof : ∀ s f, invariantsHold model s = true → TypedMachine.eval s f rule.guard = true →
      holds (obligationsFor (shorten rule) none []) s f = true ∧
      Each (fun inv => holds (obligationsFor (shorten rule) none [inv]) s f = true) affected) :
    FiringPreserves model rule none := by
  apply preserves_after_removing_text model rule none (prefixActions rule) 56
    (TypedMachine.eval initial zeroValues e807) actions untouched
  · intro s f enabled
    exact of_decide_eq_true (phase s f enabled)
  · apply preserves_touched
    intro s f valid _ enabled
    obtain ⟨total, checked⟩ := proof s f valid enabled
    refine ⟨total, ?_⟩
    intro inv member observed
    apply checked.of_mem
    rw [← catalog]
    change ignoresFiring inv (shorten rule) none = false at observed
    exact List.mem_filter.mpr ⟨member, by simp [observed]⟩

private theorem off_e489 (s : Snapshot) (f : Values)
    (est : TypedMachine.eval s f e923 = true) : TypedMachine.eval s f e489 = false := by
  have state : TypedMachine.eval s f e488 = TypedMachine.eval s f e807 := of_decide_eq_true est
  change decide (TypedMachine.eval s f e488 = TypedMachine.eval s f e14) = false
  rw [state]
  rfl

private theorem off_e580 (s : Snapshot) (f : Values)
    (est : TypedMachine.eval s f e923 = true) : TypedMachine.eval s f e580 = false := by
  have state : TypedMachine.eval s f e488 = TypedMachine.eval s f e807 := of_decide_eq_true est
  change decide (TypedMachine.eval s f e488 = TypedMachine.eval s f e579) = false
  rw [state]
  rfl

private theorem off_e743 (s : Snapshot) (f : Values)
    (est : TypedMachine.eval s f e923 = true) : TypedMachine.eval s f e743 = false := by
  have state : TypedMachine.eval s f e488 = TypedMachine.eval s f e807 := of_decide_eq_true est
  change decide (TypedMachine.eval s f e488 = TypedMachine.eval s f e568) = false
  rw [state]
  rfl

private theorem off_e810 (s : Snapshot) (f : Values)
    (est : TypedMachine.eval s f e923 = true) : TypedMachine.eval s f e810 = false := by
  have state : TypedMachine.eval s f e488 = TypedMachine.eval s f e807 := of_decide_eq_true est
  change decide (TypedMachine.eval s f e488 = TypedMachine.eval s f e740) = false
  rw [state]
  rfl

private theorem off_e955 (s : Snapshot) (f : Values)
    (est : TypedMachine.eval s f e923 = true) : TypedMachine.eval s f e955 = false := by
  have state : TypedMachine.eval s f e488 = TypedMachine.eval s f e807 := of_decide_eq_true est
  change decide (TypedMachine.eval s f e488 = TypedMachine.eval s f e940) = false
  rw [state]
  rfl

private theorem off_e959 (s : Snapshot) (f : Values)
    (est : TypedMachine.eval s f e923 = true) : TypedMachine.eval s f e959 = false := by
  have state : TypedMachine.eval s f e488 = TypedMachine.eval s f e807 := of_decide_eq_true est
  change decide (TypedMachine.eval s f e488 = TypedMachine.eval s f e958) = false
  rw [state]
  rfl

private theorem off_e944 (s : Snapshot) (f : Values)
    (est : TypedMachine.eval s f e923 = true) : TypedMachine.eval s f e944 = false := by
  have state : TypedMachine.eval s f e488 = TypedMachine.eval s f e807 := of_decide_eq_true est
  change decide (TypedMachine.eval s f e488 = TypedMachine.eval s f e943) = false
  rw [state]
  rfl

private theorem off_e962 (s : Snapshot) (f : Values)
    (est : TypedMachine.eval s f e923 = true) : TypedMachine.eval s f e962 = false := by
  have state : TypedMachine.eval s f e488 = TypedMachine.eval s f e807 := of_decide_eq_true est
  change decide (TypedMachine.eval s f e488 = TypedMachine.eval s f e961) = false
  rw [state]
  rfl

private theorem off_e964 (s : Snapshot) (f : Values)
    (est : TypedMachine.eval s f e923 = true) : TypedMachine.eval s f e964 = false := by
  have state : TypedMachine.eval s f e488 = TypedMachine.eval s f e807 := of_decide_eq_true est
  change decide (TypedMachine.eval s f e488 = TypedMachine.eval s f e947) = false
  rw [state]
  rfl

private theorem off_e967 (s : Snapshot) (f : Values)
    (est : TypedMachine.eval s f e923 = true) : TypedMachine.eval s f e967 = false := by
  have state : TypedMachine.eval s f e488 = TypedMachine.eval s f e807 := of_decide_eq_true est
  change decide (TypedMachine.eval s f e488 = TypedMachine.eval s f e966) = false
  rw [state]
  rfl

private theorem off_e1674 (s : Snapshot) (f : Values)
    (est : TypedMachine.eval s f e923 = true) : TypedMachine.eval s f e1674 = false := by
  change (((((false || TypedMachine.eval s f e743) || TypedMachine.eval s f e810) || TypedMachine.eval s f e955) || TypedMachine.eval s f e962) || TypedMachine.eval s f e964) = false
  simp only [off_e743 s f est, off_e810 s f est, off_e955 s f est, off_e962 s f est, off_e964 s f est, Bool.false_or]

private theorem off_e1702 (s : Snapshot) (f : Values)
    (est : TypedMachine.eval s f e923 = true) : TypedMachine.eval s f e1702 = false := by
  change (((false || TypedMachine.eval s f e944) || TypedMachine.eval s f e959) || TypedMachine.eval s f e967) = false
  simp only [off_e944 s f est, off_e959 s f est, off_e967 s f est, Bool.false_or]


/-- A projection of the effects seen by the affected invariants. Each rule's
generated obligations are checked against this projection below. -/
private def ackReads (fresh rearm : Bool) : ExprRewrite.Rewrite :=
  { varRead := fun kind slot =>
      match kind with
      | .octets => if slot = 41 then e1283 else .variable .octets slot
      | .sequence => if slot = 28 then e762 else .variable .sequence slot
      | .integer => if slot = 43 && fresh then e772 else .variable .integer slot
      | .boolean => .variable .boolean slot
      | .text => .variable .text slot
    field := fun kind slot => .literal kind (getValue kind zeroValues slot)
    stateIs := fun id => .literal .boolean (decide (0 = id))
    timerActive := fun owner =>
      if owner = 2 then .literal .boolean rearm else .timerActive owner }

private def ackConditions (fresh rearm : Bool) (inv : Expr .boolean) : List (Expr .boolean) :=
  (if rearm then [.intGe e566 e44] else []) ++ [ExprRewrite.run (ackReads fresh rearm) inv]

private theorem condition (s : Snapshot) (f : Values) (fresh rearm : Bool) (inv : Expr .boolean)
    (facts : DataFacts s f)
    (post : TypedMachine.eval s f (ExprRewrite.run (ackReads fresh rearm) inv) = true) :
    holds (ackConditions fresh rearm inv) s f = true := by
  cases rearm
  · change (TypedMachine.eval s f (ExprRewrite.run (ackReads fresh false) inv) && true) = true
    simp [post]
  · change (decide (1 ≤ TypedMachine.eval s f e566) &&
      (TypedMachine.eval s f (ExprRewrite.run (ackReads fresh true) inv) && true)) = true
    have delay : decide (1 ≤ TypedMachine.eval s f e566) = true := decide_eq_true facts.positiveDelay
    simp [delay, post]

private def affectedAck (fresh : Bool) : List (Expr .boolean) :=
  [e1631, e1638, e1642, e1646, e1651, e1654, e1657, e1660, e1663, e1666, e1679, e1685,
    e1687, e1690, e1691] ++ (if fresh then [e1696] else []) ++ [e1698, e1704, e1705]

private theorem ack_post (s : Snapshot) (f : Values) (fresh rearm : Bool)
    (facts : DataFacts s f)
    (activity : decide (1 ≤ leftLength s f) = rearm) :
    Each (fun inv => TypedMachine.eval s f (ExprRewrite.run (ackReads fresh rearm) inv) = true)
      (affectedAck fresh) := by
  have est := facts.ordered
  have advance : decide (TypedMachine.eval s f e763 =
      ValueOps.seqAdd (TypedMachine.eval s f e762) (leftLength s f)) = true :=
    decide_eq_true facts.sameSequence
  have buffered : decide (TypedMachine.eval s f e925 + leftLength s f ≤ 16) = true :=
    decide_eq_true facts.sendBound
  have window : decide (leftLength s f ≤ TypedMachine.eval s f (if fresh then e772 else e1221)) = true := by
    cases fresh
    · exact decide_eq_true facts.staleBound
    · exact decide_eq_true facts.freshBound
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- In every other TCP phase, these implications have a false antecedent.
  · change (!TypedMachine.eval s f e489 || _) = true
    simp [off_e489 s f est]
  · change (!TypedMachine.eval s f e580 || _) = true
    simp [off_e580 s f est]
  · change (!TypedMachine.eval s f e743 || _) = true
    simp [off_e743 s f est]
  · change (!TypedMachine.eval s f e810 || _) = true
    simp [off_e810 s f est]
  · change (!TypedMachine.eval s f e955 || _) = true
    simp [off_e955 s f est]
  · change (!TypedMachine.eval s f e959 || _) = true
    simp [off_e959 s f est]
  · change (!TypedMachine.eval s f e944 || _) = true
    simp [off_e944 s f est]
  · change (!TypedMachine.eval s f e962 || _) = true
    simp [off_e962 s f est]
  · change (!TypedMachine.eval s f e964 || _) = true
    simp [off_e964 s f est]
  · change (!TypedMachine.eval s f e967 || _) = true
    simp [off_e967 s f est]
  · change (!TypedMachine.eval s f e1674 || _) = true
    simp [off_e1674 s f est]
  · change (!TypedMachine.eval s f e743 || _) = true
    simp [off_e743 s f est]
  · change (!TypedMachine.eval s f e923 || decide (rearm = decide (1 ≤ leftLength s f))) = true
    rw [activity]
    simp [est]
  · change (!TypedMachine.eval s f e923 || decide (TypedMachine.eval s f e763 =
      ValueOps.seqAdd (TypedMachine.eval s f e762) (leftLength s f))) = true
    rw [est, advance]
    rfl
  · exact buffered
  · have noBufferedOutside : TypedMachine.eval s f (ExprRewrite.run (ackReads fresh rearm) e1698) = true := by
      change (!(!TypedMachine.eval s f e923) || _) = true
      simp [est]
    have noFlightOutside : TypedMachine.eval s f (ExprRewrite.run (ackReads fresh rearm) e1704) = true := by
      change (!TypedMachine.eval s f e1702 || _) = true
      simp [off_e1702 s f est]
    have flightWithin : TypedMachine.eval s f (ExprRewrite.run (ackReads fresh rearm) e1705) = true := by
      cases fresh <;> exact window
    cases fresh
    · exact ⟨noBufferedOutside, noFlightOutside, flightWithin, trivial⟩
    · have range := advertised_range s f
      have rangeChecked : TypedMachine.eval s f (ExprRewrite.run (ackReads true rearm) e1696) = true := by
        change ((decide (0 ≤ TypedMachine.eval s f e772)) &&
          decide (TypedMachine.eval s f e772 ≤ 65535)) = true
        simp [range.1, range.2]
      exact ⟨rangeChecked, noBufferedOutside, noFlightOutside, flightWithin, trivial⟩

private theorem ack_obligations (rule : Rule) (fresh rearm : Bool) (s : Snapshot) (f : Values)
    (align : ∀ inv ∈ affectedAck fresh,
      obligationsFor (shorten rule) none [inv] = ackConditions fresh rearm inv)
    (facts : DataFacts s f) (activity : decide (1 ≤ leftLength s f) = rearm) :
    Each (fun inv => holds (obligationsFor (shorten rule) none [inv]) s f = true) (affectedAck fresh) := by
  generalize h : affectedAck fresh = clauses
  have checked (inv) (member : inv ∈ clauses) :
      holds (obligationsFor (shorten rule) none [inv]) s f = true := by
    rw [← h] at member
    rw [align inv member]
    exact condition s f fresh rearm inv facts ((ack_post s f fresh rearm facts activity).of_mem member)
  clear h align
  induction clauses with
  | nil => trivial
  | cons inv tail ih =>
    exact ⟨checked inv (by simp), ih (fun i member => checked i (List.mem_cons_of_mem _ member))⟩
private def acknowledgmentGuard (fresh rearm : Bool) : Expr .boolean :=
  .boolAnd
    (.boolAnd e923
      (.boolAnd e812
        (.boolAnd
          (.boolAnd (.boolAnd e1264 (if rearm then e1289 else e1265)) e1268)
          (if fresh then e1278 else e1284))))
    e721

private theorem input_facts (s : Snapshot) (f : Values) (fresh rearm : Bool)
    (enabled : TypedMachine.eval s f (acknowledgmentGuard fresh rearm) = true) :
    TypedMachine.eval s f e923 = true ∧ 1 ≤ estimate s f ∧
      estimate s f ≤ outstanding s f ∧
      outstanding s f - estimate s f ≤ TypedMachine.eval s f e772 ∧
      TypedMachine.eval s f (if rearm then e1289 else e1265) = true := by
  let trim : Expr .boolean := .boolAnd e1264 (if rearm then e1289 else e1265)
  let window : Expr .boolean := .boolAnd (.boolAnd trim e1268) (if fresh then e1278 else e1284)
  have shape := (parts s f (.boolAnd e923 (.boolAnd e812 window)) e721 enabled).1
  have est := parts s f e923 (.boolAnd e812 window) shape
  have bounds := (parts s f e812 window est.2).2
  have selected := (parts s f (.boolAnd trim e1268) (if fresh then e1278 else e1284) bounds).1
  have peer := parts s f trim e1268 selected
  have bytes := parts s f e1264 (if rearm then e1289 else e1265) peer.1
  have span := (parts s f e1258 e1263 bytes.1).2
  have limits := parts s f e1261 e1262 span
  exact ⟨est.1, of_decide_eq_true (parts s f e3 e1260 limits.1).2,
    of_decide_eq_true limits.2, of_decide_eq_true peer.2, bytes.2⟩

private theorem timer_activity (s : Snapshot) (f : Values) (rearm : Bool)
    (lower : 1 ≤ estimate s f) (upper : estimate s f ≤ outstanding s f)
    (guard : TypedMachine.eval s f (if rearm then e1289 else e1265) = true) :
    decide (1 ≤ leftLength s f) = rearm := by
  cases rearm
  · have complete : estimate s f = outstanding s f := of_decide_eq_true guard
    rw [projectedLength s f lower upper, complete, Int.sub_self]
    rfl
  · change (!decide (estimate s f = outstanding s f)) = true at guard
    have strict_of_le (x y : Int) (bound : x ≤ y) (different : x ≠ y) : x < y := by omega
    have strict : estimate s f < outstanding s f :=
      strict_of_le _ _ upper (by simpa using guard)
    apply decide_eq_true
    rw [projectedLength s f lower upper]
    exact Int.add_one_le_of_lt (Int.sub_pos.mpr strict)

private theorem ack_rule (rule : Rule) (fresh rearm : Bool)
    (guard : rule.guard = acknowledgmentGuard fresh rearm)
    (actions : rule.actions = prefixActions rule ++ [.assign .text 56 e807])
    (untouched : (prefixActions rule).all (ignoresAction (.variable .text 56)) = true)
    (catalog : model.invariants.filter (fun inv => !ignoresFiring inv (shorten rule) none) = affectedAck fresh)
    (delayChecks : obligationsFor (shorten rule) none [] = if rearm then [.intGe e566 e44] else [])
    (align : (affectedAck fresh).map (fun inv => obligationsFor (shorten rule) none [inv]) =
      (affectedAck fresh).map (ackConditions fresh rearm)) :
    FiringPreserves model rule none := by
  refine certify rule actions untouched ?_ catalog ?_
  · intro s f enabled
    rw [guard] at enabled
    exact (input_facts s f fresh rearm enabled).1
  · intro s f valid enabled
    rw [guard] at enabled
    obtain ⟨phase, lower, upper, peer, selected⟩ := input_facts s f fresh rearm enabled
    have facts := data_facts s f valid phase lower upper peer
    refine ⟨?_, ack_obligations _ fresh rearm s f (List.map_inj_left.mp align) facts
      (timer_activity s f rearm lower upper selected)⟩
    rw [delayChecks]
    cases rearm
    · rfl
    · change (decide (1 ≤ TypedMachine.eval s f e566) && true) = true
      rw [decide_eq_true facts.positiveDelay]
      rfl

theorem duplicate_ack_window : Approved.raw_252_external := by
  refine certify rule_252 rfl (by decide +kernel) ?_ (affected := [e1696, e1705]) rfl ?_
  · intro s f enabled
    exact (guard_facts s f enabled).1
  · intro s f _ enabled
    have range := advertised_range s f
    refine ⟨rfl, ?_, ?_, trivial⟩
    · change ((decide (0 ≤ TypedMachine.eval s f e772) &&
        decide (TypedMachine.eval s f e772 ≤ 65535)) && true) = true
      simp [range.1, range.2]
    · change (decide (TypedMachine.eval s f e929 ≤ TypedMachine.eval s f e772) && true) = true
      simp [(guard_facts s f enabled).2]

theorem full_fresh : Approved.raw_248_external :=
  ack_rule rule_248 true false rfl rfl (by decide +kernel) rfl rfl rfl

theorem full_stale : Approved.raw_249_external :=
  ack_rule rule_249 false false rfl rfl (by decide +kernel) rfl rfl rfl

theorem partial_fresh : Approved.raw_250_external :=
  ack_rule rule_250 true true rfl rfl (by decide +kernel) rfl rfl rfl

theorem partial_stale : Approved.raw_251_external :=
  ack_rule rule_251 false true rfl rfl (by decide +kernel) rfl rfl rfl

def firings : List (Rule × Option Nat) :=
  [(rule_248, none), (rule_249, none), (rule_250, none), (rule_251, none), (rule_252, none)]

theorem checked : Each (fun p => FiringPreserves model p.1 p.2) firings :=
  ⟨full_fresh, full_stale, partial_fresh, partial_stale, duplicate_ack_window, trivial⟩

private theorem acknowledgmentMember (index : Nat) (rule : Rule)
    (selected : model.rules[index]? = some rule) (external : rule.event ∈ model.externalEvents) :
    (rule, none) ∈ rawChecks model declaredTimers :=
  raw_external_member model declaredTimers rule (List.mem_iff_getElem?.mpr ⟨index, selected⟩) external

theorem members : Each (fun p => p ∈ rawChecks model declaredTimers) firings :=
  ⟨acknowledgmentMember 248 rule_248 rfl (by decide), acknowledgmentMember 249 rule_249 rfl (by decide),
    acknowledgmentMember 250 rule_250 rfl (by decide), acknowledgmentMember 251 rule_251 rfl (by decide),
    acknowledgmentMember 252 rule_252 rfl (by decide), trivial⟩

#print axioms full_fresh
#print axioms full_stale
#print axioms partial_fresh
#print axioms partial_stale
end TCPIPAcknowledgments
