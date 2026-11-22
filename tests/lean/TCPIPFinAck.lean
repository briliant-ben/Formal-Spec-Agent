import Approved
import TCPIPQueueRelease

namespace TCPIPFinAck
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts
open EffectConditions EffectFootprint TimedObligations
set_option maxRecDepth 16384

private inductive ClosingAck where
  | finWaitOne | closing | lastAck

private def guardFor : ClosingAck → Expr .boolean
  | .finWaitOne => e975
  | .closing => e983
  | .lastAck => e989

private def source : ClosingAck → Expr .boolean
  | .finWaitOne => e955
  | .closing => e962
  | .lastAck => e964

private def sourceText : ClosingAck → Expr .text
  | .finWaitOne => e940
  | .closing => e961
  | .lastAck => e947

private def targetText : ClosingAck → Expr .text
  | .finWaitOne => e958
  | .closing => e966
  | .lastAck => e14

private def delays : ClosingAck → List (Expr .boolean)
  | .closing => [.intGe e985 e44]
  | _ => []

private def phaseHead : List (Expr .boolean) :=
  [e1631, e1634, e1637, e1638, e1639, e1640, e1642, e1644, e1645,
   e1646, e1647, e1648, e1649, e1650, e1651, e1652, e1653, e1654]

private def phaseTail : List (Expr .boolean) :=
  [e1657, e1658, e1659, e1660, e1661, e1662, e1663, e1664, e1665, e1666, e1667, e1669]

private def phaseClauses := phaseHead ++ [e1655, e1656] ++ phaseTail

private def queuePrefix : ClosingAck → List (Expr .boolean)
  | .lastAck => [e1612, e1614, e1615]
  | _ => []

private def queueSuffix : ClosingAck → List (Expr .boolean)
  | .lastAck => [e1721]
  | _ => []

private def affected (kind : ClosingAck) :=
  queuePrefix kind ++ phaseClauses ++ [e1679, e1685, e1687, e1690, e1698, e1704, e1716] ++ queueSuffix kind

private def queueChecks (kind : ClosingAck) := queuePrefix kind ++ queueSuffix kind

private def dynamics : ClosingAck → List (Expr .boolean)
  | .finWaitOne => [e1655, e1656, e1698, e1704]
  | .closing => [e1698, e1704]
  | .lastAck => [e1698]

private def retainedTimers : ClosingAck → List (Expr .boolean)
  | .finWaitOne => []
  | _ => [e1655, e1656]

private def ackedSequence : ClosingAck → List (Expr .boolean)
  | .lastAck => [e1704]
  | _ => []

private def statics (kind : ClosingAck) :=
  phaseHead ++ retainedTimers kind ++ phaseTail ++ [e1679, e1685, e1687, e1690, e1716] ++ ackedSequence kind

private def post (r : Rule) (kind : ClosingAck) (inv : Expr .boolean) :=
  (obligationsFor r none [inv]).drop (delays kind).length

private theorem both (s : Snapshot) (f : Values) (x y : Expr .boolean)
    (enabled : TypedMachine.eval s f (.boolAnd x y) = true) :
    TypedMachine.eval s f x = true ∧ TypedMachine.eval s f y = true := by
  change (TypedMachine.eval s f x && TypedMachine.eval s f y) = true at enabled
  simpa only [Bool.and_eq_true] using enabled

private theorem guard_facts (s : Snapshot) (f : Values) (kind : ClosingAck)
    (enabled : TypedMachine.eval s f (guardFor kind) = true) :
    TypedMachine.eval s f (source kind) = true ∧
      TypedMachine.eval s f e762 = TypedMachine.eval s f e763 := by
  have acknowledgment (enabled : TypedMachine.eval s f e969 = true) :
      TypedMachine.eval s f e762 = TypedMachine.eval s f e763 :=
    of_decide_eq_true (both s f e764 e813 (both s f e812 e814 enabled).2).1
  cases kind
  · have checked := both s f e955 e969 (both s f e974 e721 enabled).1
    exact ⟨checked.1, acknowledgment checked.2⟩
  · have checked := both s f e962 e969 (both s f e982 e721 enabled).1
    exact ⟨checked.1, acknowledgment checked.2⟩
  · have checked := both s f e964 e969 (both s f e988 e721 enabled).1
    exact ⟨checked.1, acknowledgment checked.2⟩

private theorem buffers_empty (s : Snapshot) (f : Values) (kind : ClosingAck)
    (valid : invariantsHold model s = true) (atSource : TypedMachine.eval s f (source kind) = true) :
    TypedMachine.eval s f e935 = true := by
  have name : TypedMachine.eval s f e488 = TypedMachine.eval initial zeroValues (sourceText kind) := by
    cases kind <;> exact of_decide_eq_true atSource
  have outside : TypedMachine.eval s zeroValues e923 = false := by
    change decide (TypedMachine.eval s f e488 = TypedMachine.eval initial zeroValues e807) = false
    rw [name]
    cases kind <;> decide
  have safe := List.all_eq_true.mp valid e1698 (by rw [model_invariants]; simp)
  change (!(!TypedMachine.eval s zeroValues e923) || TypedMachine.eval s f e935) = true at safe
  simpa only [outside, Bool.not_false, Bool.not_true, Bool.false_or] using safe

private theorem delay_valid (s : Snapshot) (f : Values) (kind : ClosingAck)
    (valid : invariantsHold model s = true) : holds (delays kind) s f = true := by
  cases kind
  · rfl
  · have positive : 1 ≤ TypedMachine.eval s f e984 :=
      of_decide_eq_true (List.all_eq_true.mp valid e1682 (by rw [model_invariants]; simp))
    have double (msl : Int) (positive : 1 ≤ msl) : 1 ≤ msl * 2 := by omega
    change (decide (1 ≤ TypedMachine.eval s f e984 * 2) && true) = true
    simp [double _ positive]
  · rfl

private theorem classify (kind : ClosingAck) (inv : Expr .boolean)
    (covered : inv ∈ affected kind) :
    inv ∈ statics kind ∨ inv ∈ dynamics kind ∨ inv ∈ queueChecks kind := by
  simp only [affected, phaseClauses, List.mem_append] at covered
  rcases covered with (((front | ((before | timers) | after)) | other) | suffix)
  · exact Or.inr (Or.inr (List.mem_append_left _ front))
  · exact Or.inl (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ before))))
  · cases kind
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at timers
      rcases timers with rfl | rfl <;> exact Or.inr (Or.inl (by simp [dynamics]))
    · exact Or.inl (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ timers))))
    · exact Or.inl (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ timers))))
  · exact Or.inl (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ after)))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at other
    rcases other with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (List.mem_append_left _ (List.mem_append_right _ (by simp)))
    · exact Or.inl (List.mem_append_left _ (List.mem_append_right _ (by simp)))
    · exact Or.inl (List.mem_append_left _ (List.mem_append_right _ (by simp)))
    · exact Or.inl (List.mem_append_left _ (List.mem_append_right _ (by simp)))
    · cases kind <;> exact Or.inr (Or.inl (by simp [dynamics]))
    · cases kind
      · exact Or.inr (Or.inl (by simp [dynamics]))
      · exact Or.inr (Or.inl (by simp [dynamics]))
      · exact Or.inl (List.mem_append_right _ (by simp [ackedSequence]))
    · exact Or.inl (List.mem_append_left _ (List.mem_append_right _ (by simp)))
  · exact Or.inr (Or.inr (List.mem_append_right _ suffix))

private def reads (kind : ClosingAck) (wireAck : Expr .sequence) : ExprRewrite.Rewrite :=
  {
    varRead := fun k slot =>
      match k with
      | .text => if slot = 56 then targetText kind else .variable .text slot
      | .sequence => if slot = 28 then wireAck else .variable .sequence slot
      | .integer => .variable .integer slot
      | .boolean => .variable .boolean slot
      | .octets => .variable .octets slot
    field := fun k slot => .literal k (getValue k zeroValues slot)
    stateIs := fun id => .literal .boolean (decide (0 = id))
    timerActive := fun id =>
      if id = 2 || (id = 4 && (match kind with | .finWaitOne => false | _ => true)) then
        .literal .boolean false
      else if id = 3 then
        match kind with
        | .finWaitOne => .timerActive id
        | .closing => .literal .boolean true
        | .lastAck => .literal .boolean false
      else .timerActive id }

private theorem fin_wait_checks (s : Snapshot) (f : Values) (wireAck : Expr .sequence)
    (user : TypedMachine.eval s f e1632 = true)
    (wait : TypedMachine.eval s f e1635 = false)
    (empty : TypedMachine.eval s f e935 = true)
    (ack : TypedMachine.eval s f wireAck = TypedMachine.eval s f e763) :
    Each (fun inv => TypedMachine.eval s f (ExprRewrite.run (reads .finWaitOne wireAck) inv) = true)
      (dynamics .finWaitOne) :=
  ⟨decide_eq_true user, decide_eq_true wait, empty, decide_eq_true ack, trivial⟩

private theorem time_wait_checks (s : Snapshot) (f : Values) (wireAck : Expr .sequence)
    (empty : TypedMachine.eval s f e935 = true)
    (ack : TypedMachine.eval s f wireAck = TypedMachine.eval s f e763) :
    Each (fun inv => TypedMachine.eval s f (ExprRewrite.run (reads .closing wireAck) inv) = true)
      (dynamics .closing) :=
  ⟨empty, decide_eq_true ack, trivial⟩

private theorem finWaitOne_checks (s : Snapshot) (f : Values)
    (valid : invariantsHold model s = true) (on : TypedMachine.eval s f (guardFor .finWaitOne) = true) :
    Each (fun inv => TypedMachine.eval s f (ExprRewrite.run (reads .finWaitOne e762) inv) = true)
      (dynamics .finWaitOne) := by
  obtain ⟨phase, ack⟩ := guard_facts s f .finWaitOne on
  have empty := buffers_empty s f .finWaitOne valid phase
  have preUser := List.all_eq_true.mp valid e1652 (by rw [model_invariants]; simp)
  have preWait := List.all_eq_true.mp valid e1653 (by rw [model_invariants]; simp)
  have atFin : TypedMachine.eval s zeroValues e955 = true := phase
  change (!TypedMachine.eval s zeroValues e955 ||
    decide (TypedMachine.eval s f e1632 = true)) = true at preUser
  change (!TypedMachine.eval s zeroValues e955 ||
    decide (TypedMachine.eval s f e1635 = false)) = true at preWait
  simp only [atFin, Bool.not_true, Bool.false_or] at preUser preWait
  exact fin_wait_checks s f e762 (of_decide_eq_true preUser) (of_decide_eq_true preWait) empty ack

private theorem closing_checks (s : Snapshot) (f : Values)
    (valid : invariantsHold model s = true) (on : TypedMachine.eval s f (guardFor .closing) = true) :
    Each (fun inv => TypedMachine.eval s f (ExprRewrite.run (reads .closing e762) inv) = true) (dynamics .closing) := by
  obtain ⟨phase, ack⟩ := guard_facts s f .closing on
  exact time_wait_checks s f e762 (buffers_empty s f .closing valid phase) ack

private theorem lastAck_checks (s : Snapshot) (f : Values)
    (valid : invariantsHold model s = true) (on : TypedMachine.eval s f (guardFor .lastAck) = true) :
    Each (fun inv => TypedMachine.eval s f (ExprRewrite.run (reads .lastAck e762) inv) = true) (dynamics .lastAck) := by
  obtain ⟨phase, _⟩ := guard_facts s f .lastAck on
  exact ⟨buffers_empty s f .lastAck valid phase, trivial⟩

private theorem dynamic_checks (s : Snapshot) (f : Values) (kind : ClosingAck)
    (valid : invariantsHold model s = true) (on : TypedMachine.eval s f (guardFor kind) = true) :
    Each (fun inv => TypedMachine.eval s f (ExprRewrite.run (reads kind e762) inv) = true) (dynamics kind) := by
  cases kind
  · exact finWaitOne_checks s f valid on
  · exact closing_checks s f valid on
  · exact lastAck_checks s f valid on

private theorem certify (r : Rule) (kind : ClosingAck)
    (guard : r.guard = guardFor kind)
    (timing : obligationsFor r none [] = delays kind)
    (catalog : model.invariants.filter (fun inv => !ignoresFiring inv r none) = affected kind)
    (staticChecks : ∀ s f, (statics kind).all (fun inv => holds (post r kind inv) s f) = true)
    (dynamic : (dynamics kind).map (post r kind) = (dynamics kind).map (fun inv => [ExprRewrite.run (reads kind e762) inv]))
    (queue : ∀ s f, invariantsHold model s = true →
      Each (fun inv => holds (post r kind inv) s f = true) (queueChecks kind)) :
    FiringPreserves model r none := by
  apply preserves_touched
  intro s f valid _ enabled
  rw [guard] at enabled
  have positive := delay_valid s f kind valid
  refine ⟨timing ▸ positive, ?_⟩
  intro inv member seen
  have covered : inv ∈ affected kind := by
    rw [← catalog]
    exact List.mem_filter.mpr ⟨member, by simp [seen]⟩
  have checked : holds (post r kind inv) s f = true := by
    rcases classify kind inv covered with static | effect | link
    · exact List.all_eq_true.mp (staticChecks s f) _ static
    · rw [List.map_inj_left.mp dynamic inv effect]
      change (TypedMachine.eval s f (ExprRewrite.run (reads kind e762) inv) && true) = true
      rw [(dynamic_checks s f kind valid enabled).of_mem effect]
      rfl
    · exact (queue s f valid).of_mem link
  rw [obligationsFor_split, timing, holds, List.all_append]
  change (holds (delays kind) s f && holds (post r kind inv) s f) = true
  simp [positive, checked]

theorem finwait1 : Approved.raw_120_external :=
  certify rule_120 .finWaitOne rfl rfl rfl (fun _ _ => rfl) rfl (fun _ _ _ => trivial)

theorem closing : Approved.raw_122_external :=
  certify rule_122 .closing rfl rfl rfl (fun _ _ => rfl) rfl (fun _ _ _ => trivial)

theorem last_ack : Approved.raw_124_external :=
  certify rule_124 .lastAck rfl rfl rfl (fun _ _ => rfl) rfl (by
    intro s f valid
    have each := TCPIPQueueRelease.release_queue_safe s f valid
    refine ⟨?_, ?_, ?_, ?_, trivial⟩
    · change (TypedMachine.eval s f (ExprRewrite.run TCPIPQueueRelease.releaseReads e1612) && true) = true
      rw [each.1]; rfl
    · change (TypedMachine.eval s f (ExprRewrite.run TCPIPQueueRelease.releaseReads e1614) && true) = true
      rw [each.2.1]; rfl
    · change (TypedMachine.eval s f (ExprRewrite.run TCPIPQueueRelease.releaseReads e1615) && true) = true
      rw [each.2.2.1]; rfl
    · change (TypedMachine.eval s f (ExprRewrite.run TCPIPQueueRelease.releaseReads e1721) && true) = true
      rw [each.2.2.2.1]; rfl)

def firings : List (Rule × Option Nat) :=
  [(rule_120, none), (rule_122, none), (rule_124, none)]

theorem checked : Each (fun p => FiringPreserves model p.1 p.2) firings :=
  ⟨finwait1, closing, last_ack, trivial⟩

end TCPIPFinAck
