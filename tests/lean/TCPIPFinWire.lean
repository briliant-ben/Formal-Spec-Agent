import Approved
import TCPIPSendWire
import SequenceFacts

namespace TCPIPFinWire
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts
open EffectConditions EffectFootprint TimedObligations TCPIPSendWire
set_option maxRecDepth 16384

private inductive FinKind where
  | localEstablished | localCloseWait | peerEstablished | peerFinWaitTwo | peerAcked | simultaneous

private def baseGuard : FinKind → Expr .boolean
  | .localEstablished => e937
  | .localCloseWait => e945
  | .peerEstablished => e997
  | .peerFinWaitTwo => e1004
  | .peerAcked => e1009
  | .simultaneous => e1015

private def sourcePhase : FinKind → Expr .boolean
  | .localEstablished | .peerEstablished => e923
  | .localCloseWait => e944
  | .peerFinWaitTwo => e959
  | .peerAcked | .simultaneous => e955

private def targetName : FinKind → Expr .text
  | .localEstablished => e940
  | .localCloseWait => e947
  | .peerEstablished => e943
  | .peerFinWaitTwo | .peerAcked => e966
  | .simultaneous => e961

private def finDelay : FinKind → List (Expr .boolean)
  | .localEstablished | .localCloseWait => [.intGe e566 e44, .intGe e567 e44]
  | .peerFinWaitTwo | .peerAcked => [.intGe e985 e44]
  | _ => []

private def delays (kind : FinKind) (phase : LinkPhase) :=
  (match phase with | .empty => [.intGe e10 e44] | _ => []) ++ finDelay kind

private def phaseBefore : List (Expr .boolean) :=
  [e1631, e1634, e1637, e1638, e1639, e1640, e1642, e1644, e1645, e1646, e1647, e1648, e1649,
   e1650, e1651, e1652]

private def phaseAfter : List (Expr .boolean) :=
  [e1666, e1667, e1669]

private def phaseCommon :=
  phaseBefore ++ [e1653, e1654, e1655, e1656, e1657, e1658, e1659, e1660, e1661, e1662,
    e1663, e1664, e1665] ++ phaseAfter

private def retransmitCount : FinKind → List (Expr .boolean)
  | .localEstablished | .localCloseWait => [e1681]
  | _ => []

private def tcpClauses (kind : FinKind) :=
  phaseCommon ++ [e1679] ++ retransmitCount kind ++ [e1685, e1687, e1690, e1698, e1704]

private def linkPrefix : LinkPhase → List (Expr .boolean)
  | .empty => [e1594, e1597, e1601, e1604, e1612, e1614, e1615, e1628]
  | .pending => [e1612, e1614, e1615]
  | .resolved => []

private def linkSuffix : LinkPhase → List (Expr .boolean)
  | .empty | .pending => [e1721]
  | .resolved => []

private def affectedFin (kind : FinKind) (phase : LinkPhase) :=
  linkPrefix phase ++ tcpClauses kind ++ [e1706, e1716] ++ linkSuffix phase

private def post (r : Rule) (kind : FinKind) (phase : LinkPhase) (inv : Expr .boolean) :=
  (obligationsFor r none [inv]).drop (delays kind phase).length

private theorem both (s : Snapshot) (f : Values) (x y : Expr .boolean)
    (enabled : TypedMachine.eval s f (.boolAnd x y) = true) :
    TypedMachine.eval s f x = true ∧ TypedMachine.eval s f y = true := by
  change (TypedMachine.eval s f x && TypedMachine.eval s f y) = true at enabled
  simpa only [Bool.and_eq_true] using enabled

private theorem source_phase (s : Snapshot) (f : Values) (kind : FinKind)
    (on : TypedMachine.eval s f (baseGuard kind) = true) :
    TypedMachine.eval s zeroValues (sourcePhase kind) = true := by
  cases kind
  · exact (both s f e923 e936 on).1
  · exact (both s f e944 e3 on).1
  · exact (both s f e923 e995 (both s f e996 e721 on).1).1
  · exact (both s f e959 e1002 (both s f e1003 e721 on).1).1
  · exact (both s f e955 e1002 (both s f e1008 e721 on).1).1
  · exact (both s f e955 e1013 (both s f e1014 e721 on).1).1

private theorem buffers_empty (s : Snapshot) (f : Values) (kind : FinKind)
    (valid : invariantsHold model s = true) (on : TypedMachine.eval s f (baseGuard kind) = true) :
    TypedMachine.eval s f e935 = true := by
  have pre (name : Expr .text)
      (atSource : TypedMachine.eval s f e488 = TypedMachine.eval initial zeroValues name)
      (distinct : TypedMachine.eval initial zeroValues name ≠ TypedMachine.eval initial zeroValues e807) :
      TypedMachine.eval s f e935 = true := by
    have outside : TypedMachine.eval s zeroValues e923 = false := by
      change decide (TypedMachine.eval s f e488 = TypedMachine.eval initial zeroValues e807) = false
      rw [atSource]
      exact decide_eq_false distinct
    have check := List.all_eq_true.mp valid e1698 (by rw [model_invariants]; simp)
    change (!(!TypedMachine.eval s zeroValues e923) || TypedMachine.eval s f e935) = true at check
    simpa only [outside, Bool.not_false, Bool.not_true, Bool.false_or] using check
  have phase := source_phase s f kind on
  cases kind
  · exact (both s f e3 e935 (both s f e923 e936 on).2).2
  · exact pre e943 (of_decide_eq_true phase) (by decide)
  · exact (both s f e814 e935
      (both s f e993 e994 (both s f e923 e995 (both s f e996 e721 on).1).2).2).2
  · exact pre e958 (of_decide_eq_true phase) (by decide)
  · exact pre e940 (of_decide_eq_true phase) (by decide)
  · exact pre e940 (of_decide_eq_true phase) (by decide)

private theorem implication (s : Snapshot) (phase body : Expr .boolean)
    (valid : invariantsHold model s = true) (member : .implies phase body ∈ model.invariants)
    (on : TypedMachine.eval s zeroValues phase = true) : TypedMachine.eval s zeroValues body = true := by
  have clause := List.all_eq_true.mp valid _ member
  change (!TypedMachine.eval s zeroValues phase || TypedMachine.eval s zeroValues body) = true at clause
  simpa only [on, Bool.not_true, Bool.false_or] using clause

private theorem una_established (s : Snapshot) (f : Values)
    (valid : invariantsHold model s = true)
    (phase : TypedMachine.eval s zeroValues e923 = true) (empty : TypedMachine.eval s f e935 = true) :
    TypedMachine.eval s f e976 = TypedMachine.eval s f e763 := by
  have relation : TypedMachine.eval s f e763 =
      ValueOps.seqAdd (TypedMachine.eval s f e976) (TypedMachine.eval s f e929) :=
    of_decide_eq_true (implication s e923 e1689 valid
      (show e1690 ∈ model.invariants from by rw [model_invariants]; simp) phase)
  have zero : TypedMachine.eval s f e929 = 0 :=
    of_decide_eq_true (both s f e927 e930 (both s f e931 e934 empty).1).2
  have seq_zero (seq : ValueOps.Seq32) : ValueOps.seqAdd seq 0 = seq := by
    have dist : ValueOps.seqDistance seq seq = 0 := by simp [ValueOps.seqDistance]
    simpa only [dist] using SequenceFacts.add_distance seq seq
  rw [zero, seq_zero] at relation
  exact relation.symm

private theorem una_other (s : Snapshot) (f : Values) (valid : invariantsHold model s = true)
    (on : TypedMachine.eval s zeroValues e944 = true ∨ TypedMachine.eval s zeroValues e959 = true) :
    TypedMachine.eval s f e976 = TypedMachine.eval s f e763 := by
  have enabled : TypedMachine.eval s zeroValues e1702 = true := by
    change (((false || TypedMachine.eval s zeroValues e944) ||
      TypedMachine.eval s zeroValues e959) || TypedMachine.eval s zeroValues e967) = true
    rcases on with h | h <;> simp [h]
  exact of_decide_eq_true (implication s e1702 e1703 valid
    (show e1704 ∈ model.invariants from by rw [model_invariants]; simp) enabled)

private theorem finwait_control (s : Snapshot) (f : Values) (valid : invariantsHold model s = true)
    (on : TypedMachine.eval s zeroValues e955 = true) : TypedMachine.eval s f e1678 = true := by
  have enabled : TypedMachine.eval s zeroValues e1674 = true := by
    change (((((false || TypedMachine.eval s zeroValues e743) ||
      TypedMachine.eval s zeroValues e810) || TypedMachine.eval s zeroValues e955) ||
      TypedMachine.eval s zeroValues e962) || TypedMachine.eval s zeroValues e964) = true
    simp [on]
  exact implication s e1674 e1678 valid (show e1679 ∈ model.invariants from by rw [model_invariants]; simp) enabled

private theorem ack_equals_next (s : Snapshot) (f : Values)
    (on : TypedMachine.eval s f e1009 = true) :
    TypedMachine.eval s f e762 = TypedMachine.eval s f e763 := by
  have body := (both s f e955 e1002 (both s f e1008 e721 on).1).2
  exact of_decide_eq_true (both s f e764 e813 (both s f e993 e814 body).2).1

private def reads (kind : FinKind) (wireAck : Expr .sequence := e762) : ExprRewrite.Rewrite :=
  { varRead := fun k slot =>
      match k with
      | .text => if slot = 56 then targetName kind else .variable .text slot
      | .sequence => match kind with
        | .localEstablished | .localCloseWait =>
          if slot = 31 then e763 else if slot = 29 then e939 else .variable .sequence slot
        | .peerAcked => if slot = 28 then wireAck else .variable .sequence slot
        | _ => .variable .sequence slot
      | .integer => .variable .integer slot
      | .boolean => .variable .boolean slot
      | .octets => .variable .octets slot
    field := fun k slot => .literal k (getValue k zeroValues slot)
    stateIs := fun id => .literal .boolean (decide (0 = id))
    timerActive := fun id => match kind with
      | .localEstablished | .localCloseWait =>
        if id = 2 || id = 4 then .literal .boolean true else .timerActive id
      | .peerFinWaitTwo | .peerAcked =>
        if id = 2 || id = 4 then .literal .boolean false
        else if id = 3 then .literal .boolean true else .timerActive id
      | _ => .timerActive id }

private def dynamics : List (Expr .boolean) :=
  [e1653, e1657, e1658, e1659, e1660, e1661, e1662, e1665, e1679, e1698, e1704]

set_option maxHeartbeats 25000 in
private theorem localEstablished_checks (s : Snapshot) (f : Values)
    (valid : invariantsHold model s = true) (on : TypedMachine.eval s f (baseGuard .localEstablished) = true) :
    Each (fun inv => TypedMachine.eval s f (ExprRewrite.run (reads .localEstablished) inv) = true) dynamics := by
  have phase := source_phase s f .localEstablished on
  have empty := buffers_empty s f .localEstablished valid on
  have stopped := implication s e923 e1636 valid
    (show e1650 ∈ model.invariants from by rw [model_invariants]; simp) phase
  have aligned := una_established s f valid phase empty
  refine ⟨stopped, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, empty, rfl, trivial⟩
  change (decide (ValueOps.seqAdd (TypedMachine.eval s f e763) 1 =
      ValueOps.seqAdd (TypedMachine.eval s f e763) 1) &&
    decide (TypedMachine.eval s f e976 = TypedMachine.eval s f e763)) = true
  rw [decide_eq_true aligned, decide_eq_true rfl]
  rfl

set_option maxHeartbeats 25000 in
private theorem localCloseWait_checks (s : Snapshot) (f : Values)
    (valid : invariantsHold model s = true) (on : TypedMachine.eval s f (baseGuard .localCloseWait) = true) :
    Each (fun inv => TypedMachine.eval s f (ExprRewrite.run (reads .localCloseWait) inv) = true) dynamics := by
  have phase := source_phase s f .localCloseWait on
  have empty := buffers_empty s f .localCloseWait valid on
  have stopped := implication s e944 e1636 valid
    (show e1659 ∈ model.invariants from by rw [model_invariants]; simp) phase
  have aligned := una_other s f valid (Or.inl phase)
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, stopped, ?_, empty, rfl, trivial⟩
  change (decide (ValueOps.seqAdd (TypedMachine.eval s f e763) 1 =
      ValueOps.seqAdd (TypedMachine.eval s f e763) 1) &&
    decide (TypedMachine.eval s f e976 = TypedMachine.eval s f e763)) = true
  rw [decide_eq_true aligned, decide_eq_true rfl]
  rfl

set_option maxHeartbeats 25000 in
private theorem peerEstablished_checks (s : Snapshot) (f : Values)
    (valid : invariantsHold model s = true) (on : TypedMachine.eval s f (baseGuard .peerEstablished) = true) :
    Each (fun inv => TypedMachine.eval s f (ExprRewrite.run (reads .peerEstablished) inv) = true) dynamics := by
  have phase := source_phase s f .peerEstablished on
  have empty := buffers_empty s f .peerEstablished valid on
  have checked := List.all_eq_true.mp valid e1687 (by rw [model_invariants]; simp)
  change (!TypedMachine.eval s zeroValues e923 ||
    decide (TypedMachine.eval s f e1629 = decide (1 ≤ TypedMachine.eval s f e929))) = true at checked
  have zero : TypedMachine.eval s f e929 = 0 :=
    of_decide_eq_true (both s f e927 e930 (both s f e931 e934 empty).1).2
  have established : TypedMachine.eval s zeroValues e923 = true := phase
  rw [established, zero] at checked
  have rtxStopped : TypedMachine.eval s f e1629 = false := by
    change decide (TypedMachine.eval s f e1629 = false) = true at checked
    exact of_decide_eq_true checked
  have stoppedUser := implication s e923 e1633 valid
    (show e1649 ∈ model.invariants from by rw [model_invariants]; simp) phase
  have stoppedWait := implication s e923 e1636 valid
    (show e1650 ∈ model.invariants from by rw [model_invariants]; simp) phase
  have aligned := una_established s f valid phase empty
  exact ⟨rfl, decide_eq_true rtxStopped, stoppedUser, stoppedWait, rfl, rfl, rfl, rfl, rfl, empty,
    decide_eq_true aligned, trivial⟩

set_option maxHeartbeats 25000 in
private theorem peerFinWaitTwo_checks (s : Snapshot) (f : Values)
    (valid : invariantsHold model s = true) (on : TypedMachine.eval s f (baseGuard .peerFinWaitTwo) = true) :
    Each (fun inv => TypedMachine.eval s f (ExprRewrite.run (reads .peerFinWaitTwo) inv) = true) dynamics := by
  have phase := source_phase s f .peerFinWaitTwo on
  have empty := buffers_empty s f .peerFinWaitTwo valid on
  have aligned := una_other s f valid (Or.inr phase)
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, empty, decide_eq_true aligned, trivial⟩

private theorem peer_acked_clause (s : Snapshot) (f : Values) (wireAck : Expr .sequence)
    (empty : TypedMachine.eval s f e935 = true)
    (ack : TypedMachine.eval s f wireAck = TypedMachine.eval s f e763) :
    Each (fun inv => TypedMachine.eval s f (ExprRewrite.run (reads .peerAcked wireAck) inv) = true) dynamics :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, empty, decide_eq_true ack, trivial⟩

private theorem peerAcked_checks (s : Snapshot) (f : Values)
    (valid : invariantsHold model s = true) (on : TypedMachine.eval s f (baseGuard .peerAcked) = true) :
    Each (fun inv => TypedMachine.eval s f (ExprRewrite.run (reads .peerAcked) inv) = true) dynamics :=
  peer_acked_clause s f e762 (buffers_empty s f .peerAcked valid on) (ack_equals_next s f on)

set_option maxHeartbeats 25000 in
private theorem simultaneous_checks (s : Snapshot) (f : Values)
    (valid : invariantsHold model s = true) (on : TypedMachine.eval s f (baseGuard .simultaneous) = true) :
    Each (fun inv => TypedMachine.eval s f (ExprRewrite.run (reads .simultaneous) inv) = true) dynamics := by
  have phase := source_phase s f .simultaneous on
  have empty := buffers_empty s f .simultaneous valid on
  have retransmit := implication s e955 e1641 valid
    (show e1651 ∈ model.invariants from by rw [model_invariants]; simp) phase
  have user := implication s e955 e1643 valid
    (show e1652 ∈ model.invariants from by rw [model_invariants]; simp) phase
  have wait := implication s e955 e1636 valid
    (show e1653 ∈ model.invariants from by rw [model_invariants]; simp) phase
  exact ⟨rfl, rfl, rfl, rfl, retransmit, user, wait, rfl, finwait_control s f valid phase, empty, rfl, trivial⟩

private theorem dynamic_checks (s : Snapshot) (f : Values) (kind : FinKind)
    (valid : invariantsHold model s = true) (on : TypedMachine.eval s f (baseGuard kind) = true) :
    Each (fun inv => TypedMachine.eval s f (ExprRewrite.run (reads kind) inv) = true) dynamics := by
  cases kind
  · exact localEstablished_checks s f valid on
  · exact localCloseWait_checks s f valid on
  · exact peerEstablished_checks s f valid on
  · exact peerFinWaitTwo_checks s f valid on
  · exact peerAcked_checks s f valid on
  · exact simultaneous_checks s f valid on

private theorem delay_valid (s : Snapshot) (f : Values) (kind : FinKind) (phase : LinkPhase)
    (valid : invariantsHold model s = true) : holds (delays kind phase) s f = true := by
  have rto : 1000 ≤ TypedMachine.eval s f e566 :=
    of_decide_eq_true (List.all_eq_true.mp valid e1680 (by rw [model_invariants]; simp))
  have retransmit : 1 ≤ TypedMachine.eval s f e566 := Int.le_trans (by decide) rto
  have user : 1 ≤ TypedMachine.eval s f e567 :=
    of_decide_eq_true (List.all_eq_true.mp valid e1683 (by rw [model_invariants]; simp))
  have msl : 1 ≤ TypedMachine.eval s f e984 :=
    of_decide_eq_true (List.all_eq_true.mp valid e1682 (by rw [model_invariants]; simp))
  have double (msl : Int) (positive : 1 ≤ msl) : 1 ≤ msl * 2 := by omega
  have timeWait := double _ msl
  have noWait (phase : LinkPhase) :
      holds ((match phase with | .empty => [.intGe e10 e44] | _ => []) : List (Expr .boolean)) s f = true := by
    cases phase <;> rfl
  have bound : holds (finDelay kind) s f = true := by
    cases kind
    · change (decide (1 ≤ TypedMachine.eval s f e566) &&
        (decide (1 ≤ TypedMachine.eval s f e567) && true)) = true
      simp [retransmit, user]
    · change (decide (1 ≤ TypedMachine.eval s f e566) &&
        (decide (1 ≤ TypedMachine.eval s f e567) && true)) = true
      simp [retransmit, user]
    · rfl
    · change (decide (1 ≤ TypedMachine.eval s f e984 * 2) && true) = true
      simp [timeWait]
    · change (decide (1 ≤ TypedMachine.eval s f e984 * 2) && true) = true
      simp [timeWait]
    · rfl
  have append (left right : List (Expr .boolean)) :
      holds (left ++ right) s f = (holds left s f && holds right s f) := by
    exact List.all_append
  exact (append (match phase with | .empty => [.intGe e10 e44] | _ => []) (finDelay kind)).trans
    (by rw [noWait phase, bound]; rfl)

private def statics (kind : FinKind) :=
  phaseBefore ++ [e1654, e1655, e1656, e1663, e1664] ++ phaseAfter ++ retransmitCount kind ++
    [e1685, e1687, e1690, e1716]

private theorem tcp_classes (kind : FinKind) (inv : Expr .boolean)
    (covered : inv ∈ tcpClauses kind) :
    inv ∈ statics kind ∨ inv ∈ dynamics := by
  simp only [tcpClauses, phaseCommon, List.mem_append] at covered
  rcases covered with (((((before | middle) | after) | sequence) | retries) | tail)
  · exact Or.inl (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ before))))
  · have middleStatic (h : inv ∈ [e1654, e1655, e1656, e1663, e1664]) :
        inv ∈ statics kind :=
      List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ h)))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at middle
    rcases middle with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr (by simp [dynamics])
    · exact Or.inl (middleStatic (by simp))
    · exact Or.inl (middleStatic (by simp))
    · exact Or.inl (middleStatic (by simp))
    · exact Or.inr (by simp [dynamics])
    · exact Or.inr (by simp [dynamics])
    · exact Or.inr (by simp [dynamics])
    · exact Or.inr (by simp [dynamics])
    · exact Or.inr (by simp [dynamics])
    · exact Or.inr (by simp [dynamics])
    · exact Or.inl (middleStatic (by simp))
    · exact Or.inl (middleStatic (by simp))
    · exact Or.inr (by simp [dynamics])
  · exact Or.inl (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ after)))
  · obtain rfl := List.mem_singleton.mp sequence
    exact Or.inr (by simp [dynamics])
  · exact Or.inl (List.mem_append_left _ (List.mem_append_right _ retries))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at tail
    rcases tail with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (List.mem_append_right _ (by simp))
    · exact Or.inl (List.mem_append_right _ (by simp))
    · exact Or.inl (List.mem_append_right _ (by simp))
    · exact Or.inr (by simp [dynamics])
    · exact Or.inr (by simp [dynamics])

private theorem link_member (phase : LinkPhase) (inv : Expr .boolean)
    (covered : inv ∈ linkPrefix phase ∨ inv ∈ linkSuffix phase) :
    inv ∈ linkClauses phase := by
  rcases covered with front | suffix
  · cases phase
    · simp only [linkPrefix, linkClauses, List.mem_cons, List.not_mem_nil, or_false] at front ⊢
      rcases front with h | h | h | h | h | h | h | h <;> simp only [h, true_or, or_true]
    · simp only [linkPrefix, linkClauses, List.mem_cons, List.not_mem_nil, or_false] at front ⊢
      rcases front with h | h | h <;> simp only [h, true_or, or_true]
    · exact False.elim (List.not_mem_nil front)
  · cases phase
    · obtain rfl := List.mem_singleton.mp suffix
      simp [linkClauses]
    · obtain rfl := List.mem_singleton.mp suffix
      simp [linkClauses]
    · exact False.elim (List.not_mem_nil suffix)

private theorem classify (kind : FinKind) (phase : LinkPhase) (inv : Expr .boolean)
    (covered : inv ∈ affectedFin kind phase) :
    inv ∈ statics kind ∨ inv ∈ dynamics ∨ inv ∈ linkClauses phase ∨ inv = e1706 := by
  simp only [affectedFin, List.mem_append] at covered
  rcases covered with (((front | core) | tail) | suffix)
  · exact Or.inr (Or.inr (Or.inl (link_member phase inv (Or.inl front))))
  · rcases tcp_classes kind inv core with static | dynamic
    · exact Or.inl static
    · exact Or.inr (Or.inl dynamic)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at tail
    rcases tail with packet | rfl
    · exact Or.inr (Or.inr (Or.inr packet))
    · exact Or.inl (List.mem_append_right _ (by simp))
  · exact Or.inr (Or.inr (Or.inl (link_member phase inv (Or.inr suffix))))

private theorem certify (r : Rule) (kind : FinKind) (phase : LinkPhase)
    (guard : r.guard = .boolAnd (baseGuard kind) (linkGuard phase))
    (timing : obligationsFor r none [] = delays kind phase)
    (catalog : model.invariants.filter (fun inv => !ignoresFiring inv r none) = affectedFin kind phase)
    (staticChecks : ∀ s f, (statics kind).all (fun inv => holds (post r kind phase inv) s f) = true)
    (dynamic : dynamics.map (post r kind phase) = dynamics.map (fun inv => [ExprRewrite.run (reads kind) inv]))
    (ready : linkCondition (post r kind phase) phase)
    (packet : (post r kind phase e1706).all OctetBounds.certifies = true) :
    FiringPreserves model r none := by
  apply preserves_touched
  intro s f valid _ enabled
  rw [guard] at enabled
  obtain ⟨base, link⟩ := both s f _ _ enabled
  have positive := delay_valid s f kind phase valid
  refine ⟨timing ▸ positive, ?_⟩
  intro inv member seen
  have covered : inv ∈ affectedFin kind phase := by
    rw [← catalog]
    exact List.mem_filter.mpr ⟨member, by simp [seen]⟩
  have checked : holds (post r kind phase inv) s f = true := by
    rcases classify kind phase inv covered with static | effect | ethernet | rfl
    · exact List.all_eq_true.mp (staticChecks s f) _ static
    · rw [List.map_inj_left.mp dynamic inv effect]
      change (TypedMachine.eval s f (ExprRewrite.run (reads kind) inv) && true) = true
      simp [(dynamic_checks s f kind valid base).of_mem effect]
    · exact (link_checks s f _ phase ready link valid).of_mem ethernet
    · exact OctetBounds.all_sound _ (context s f) packet
  rw [obligationsFor_split, timing, holds, List.all_append]
  change (holds (delays kind phase) s f && holds (post r kind phase inv) s f) = true
  simp [positive, checked]

theorem local_established_empty : Approved.raw_105_external :=
  certify rule_105 .localEstablished .empty rfl rfl rfl (fun _ _ => rfl) rfl
    ⟨⟨by decide +kernel, by decide +kernel, rfl⟩, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩⟩
    (by decide +kernel)

theorem local_established_pending : Approved.raw_106_external :=
  certify rule_106 .localEstablished .pending rfl rfl rfl (fun _ _ => rfl) rfl
    ⟨by decide +kernel, by decide +kernel, rfl⟩
    (by decide +kernel)

theorem local_established_resolved : Approved.raw_107_external :=
  certify rule_107 .localEstablished .resolved rfl rfl rfl (fun _ _ => rfl) rfl
    trivial
    (by decide +kernel)

theorem local_close_wait_empty : Approved.raw_108_external :=
  certify rule_108 .localCloseWait .empty rfl rfl rfl (fun _ _ => rfl) rfl
    ⟨⟨by decide +kernel, by decide +kernel, rfl⟩, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩⟩
    (by decide +kernel)

theorem local_close_wait_pending : Approved.raw_109_external :=
  certify rule_109 .localCloseWait .pending rfl rfl rfl (fun _ _ => rfl) rfl
    ⟨by decide +kernel, by decide +kernel, rfl⟩
    (by decide +kernel)

theorem local_close_wait_resolved : Approved.raw_110_external :=
  certify rule_110 .localCloseWait .resolved rfl rfl rfl (fun _ _ => rfl) rfl
    trivial
    (by decide +kernel)

theorem peer_established_empty : Approved.raw_126_external :=
  certify rule_126 .peerEstablished .empty rfl rfl rfl (fun _ _ => rfl) rfl
    ⟨⟨by decide +kernel, by decide +kernel, rfl⟩, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩⟩
    (by decide +kernel)

theorem peer_established_pending : Approved.raw_127_external :=
  certify rule_127 .peerEstablished .pending rfl rfl rfl (fun _ _ => rfl) rfl
    ⟨by decide +kernel, by decide +kernel, rfl⟩
    (by decide +kernel)

theorem peer_established_resolved : Approved.raw_128_external :=
  certify rule_128 .peerEstablished .resolved rfl rfl rfl (fun _ _ => rfl) rfl
    trivial
    (by decide +kernel)

theorem peer_fin_wait_two_empty : Approved.raw_129_external :=
  certify rule_129 .peerFinWaitTwo .empty rfl rfl rfl (fun _ _ => rfl) rfl
    ⟨⟨by decide +kernel, by decide +kernel, rfl⟩, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩⟩
    (by decide +kernel)

theorem peer_fin_wait_two_pending : Approved.raw_130_external :=
  certify rule_130 .peerFinWaitTwo .pending rfl rfl rfl (fun _ _ => rfl) rfl
    ⟨by decide +kernel, by decide +kernel, rfl⟩
    (by decide +kernel)

theorem peer_fin_wait_two_resolved : Approved.raw_131_external :=
  certify rule_131 .peerFinWaitTwo .resolved rfl rfl rfl (fun _ _ => rfl) rfl
    trivial
    (by decide +kernel)

theorem peer_acked_empty : Approved.raw_132_external :=
  certify rule_132 .peerAcked .empty rfl rfl rfl (fun _ _ => rfl) rfl
    ⟨⟨by decide +kernel, by decide +kernel, rfl⟩, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩⟩
    (by decide +kernel)

theorem peer_acked_pending : Approved.raw_133_external :=
  certify rule_133 .peerAcked .pending rfl rfl rfl (fun _ _ => rfl) rfl
    ⟨by decide +kernel, by decide +kernel, rfl⟩
    (by decide +kernel)

theorem peer_acked_resolved : Approved.raw_134_external :=
  certify rule_134 .peerAcked .resolved rfl rfl rfl (fun _ _ => rfl) rfl
    trivial
    (by decide +kernel)

theorem simultaneous_empty : Approved.raw_135_external :=
  certify rule_135 .simultaneous .empty rfl rfl rfl (fun _ _ => rfl) rfl
    ⟨⟨by decide +kernel, by decide +kernel, rfl⟩, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩⟩
    (by decide +kernel)

theorem simultaneous_pending : Approved.raw_136_external :=
  certify rule_136 .simultaneous .pending rfl rfl rfl (fun _ _ => rfl) rfl
    ⟨by decide +kernel, by decide +kernel, rfl⟩
    (by decide +kernel)

theorem simultaneous_resolved : Approved.raw_137_external :=
  certify rule_137 .simultaneous .resolved rfl rfl rfl (fun _ _ => rfl) rfl
    trivial
    (by decide +kernel)

def firings : List (Rule × Option Nat) :=
  [(rule_105, none), (rule_106, none), (rule_107, none), (rule_108, none), (rule_109, none), (rule_110,
   none), (rule_126, none), (rule_127, none), (rule_128, none), (rule_129, none), (rule_130, none),
   (rule_131, none), (rule_132, none), (rule_133, none), (rule_134, none), (rule_135, none), (rule_136,
   none), (rule_137, none)]

theorem checked : Each (fun p => FiringPreserves model p.1 p.2) firings :=
  ⟨local_established_empty, local_established_pending, local_established_resolved,
   local_close_wait_empty, local_close_wait_pending, local_close_wait_resolved, peer_established_empty,
   peer_established_pending, peer_established_resolved, peer_fin_wait_two_empty,
   peer_fin_wait_two_pending, peer_fin_wait_two_resolved, peer_acked_empty, peer_acked_pending,
   peer_acked_resolved, simultaneous_empty, simultaneous_pending, simultaneous_resolved, trivial⟩

end TCPIPFinWire
