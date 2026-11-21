import Approved
import TCPIPSendWire

namespace TCPIPOpen
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts
open EffectConditions EffectFootprint TimedObligations TCPIPSendWire
set_option maxRecDepth 16384

private inductive OpenKind where
  | active | passive | simultaneous

private def guardFor : OpenKind → Expr .boolean
  | .active => e490
  | .passive => e722
  | .simultaneous => e745

private def inputPhase : OpenKind → Expr .boolean
  | .active => e489
  | .passive => e580
  | .simultaneous => e743

private def delays (kind : OpenKind) (phase : LinkPhase) : List (Expr .boolean) :=
  (match phase with | .empty => [.intGe e10 e44] | _ => []) ++
    (match kind with | .simultaneous => [] | _ => [.intGe e10 e44, .intGe e567 e44])

private def changedTimeout : OpenKind → List (Expr .boolean)
  | .simultaneous => []
  | _ => [e1680, e1681]

private def phaseBefore : List (Expr .boolean) :=
  [e1631, e1634, e1637, e1638, e1639, e1640, e1642, e1644, e1645]

private def phaseAfter : List (Expr .boolean) :=
  [e1649, e1650, e1651, e1652, e1653, e1654, e1655, e1656, e1657, e1658, e1659,
   e1660, e1661, e1662, e1663, e1664, e1665, e1666, e1667, e1669]

private def phaseClauses := phaseBefore ++ [e1646, e1647, e1648] ++ phaseAfter

private def tcpClauses (kind : OpenKind) :=
  phaseClauses ++ [e1679] ++ changedTimeout kind ++ [e1685, e1687, e1690, e1698, e1704]

private def affectedOpen (kind : OpenKind) (phase : LinkPhase) : List (Expr .boolean) :=
  match phase with
  | .empty => [e1594, e1597, e1601, e1604, e1612, e1614, e1615, e1628] ++
      tcpClauses kind ++ [e1706, e1716, e1721]
  | .pending => [e1612, e1614, e1615] ++ tcpClauses kind ++ [e1706, e1716, e1721]
  | .resolved => tcpClauses kind ++ [e1706, e1716]

private def staticClauses (kind : OpenKind) : List (Expr .boolean) :=
  phaseBefore ++ phaseAfter ++ changedTimeout kind ++ [e1687, e1690, e1704, e1716]

private def dynamicClauses : List (Expr .boolean) := [e1646, e1647, e1648, e1679, e1685, e1698]

private theorem split_ands (s : Snapshot) (f : Values) (a b : Expr .boolean)
    (on : TypedMachine.eval s f (.boolAnd a b) = true) :
    TypedMachine.eval s f a = true ∧ TypedMachine.eval s f b = true := by
  change (TypedMachine.eval s f a && TypedMachine.eval s f b) = true at on
  simpa only [Bool.and_eq_true] using on

private theorem guard_phase (s : Snapshot) (f : Values) (kind : OpenKind)
    (on : TypedMachine.eval s f (guardFor kind) = true) :
    TypedMachine.eval s f (inputPhase kind) = true := by
  cases kind
  · exact (split_ands s f e489 e3 on).1
  · exact (split_ands s f e580 e672 (split_ands s f e673 e721 on).1).1
  · exact (split_ands s f e743 e672 (split_ands s f e744 e721 on).1).1

private theorem buffers_empty (s : Snapshot) (f : Values) (kind : OpenKind)
    (valid : invariantsHold model s = true) (on : TypedMachine.eval s f (inputPhase kind) = true) :
    TypedMachine.eval s f e935 = true := by
  have other (phase : String) (phaseMatches : TypedMachine.eval s f e488 = phase)
      (different : phase ≠ TypedMachine.eval initial zeroValues e807) :
      TypedMachine.eval s zeroValues e923 = false := by
    change decide (TypedMachine.eval s f e488 = TypedMachine.eval initial zeroValues e807) = false
    rw [phaseMatches]
    exact decide_eq_false different
  have notEstablished : TypedMachine.eval s zeroValues e923 = false := by
    cases kind
    · exact other (TypedMachine.eval initial zeroValues e14) (of_decide_eq_true on) (by decide)
    · exact other (TypedMachine.eval initial zeroValues e579) (of_decide_eq_true on) (by decide)
    · exact other (TypedMachine.eval initial zeroValues e568) (of_decide_eq_true on) (by decide)
  have prior := List.all_eq_true.mp valid e1698 (by rw [model_invariants]; simp)
  change (!(!TypedMachine.eval s zeroValues e923) || TypedMachine.eval s zeroValues e935) = true at prior
  simp only [notEstablished, Bool.not_false, Bool.not_true, Bool.false_or] at prior
  exact prior

private def nextPhase : OpenKind → Expr .text
  | .active => e568
  | _ => e740

private def reads (kind : OpenKind) : ExprRewrite.Rewrite :=
  { varRead := fun k slot =>
      match k with
      | .text => if slot = 56 then nextPhase kind else .variable .text slot
      | .sequence => match kind with
        | .simultaneous => if slot = 31 then e492 else .variable .sequence slot
        | _ => if slot = 28 || slot = 31 then e492 else if slot = 29 then e493 else .variable .sequence slot
      | .integer => .variable .integer slot
      | .boolean => .variable .boolean slot
      | .octets => .variable .octets slot
    field := fun k slot => .literal k (getValue k zeroValues slot)
    stateIs := fun id => .literal .boolean (decide (0 = id))
    timerActive := fun id =>
      match kind with
      | .active =>
        if id = 2 || id = 4 then .literal .boolean true else
        if id = 3 then .literal .boolean false else .timerActive id
      | .passive => if id = 2 || id = 4 then .literal .boolean true else .timerActive id
      | .simultaneous => .timerActive id }

private theorem timer_from (s : Snapshot) (phase timer : Expr .boolean) (value : Bool)
    (valid : invariantsHold model s = true)
    (member : .implies phase (.equal .boolean timer (.literal .boolean value)) ∈ model.invariants)
    (on : TypedMachine.eval s zeroValues phase = true) :
    TypedMachine.eval s zeroValues timer = value := by
  have checked := List.all_eq_true.mp valid _ member
  change (!TypedMachine.eval s zeroValues phase ||
    decide (TypedMachine.eval s zeroValues timer = value)) = true at checked
  simp only [on, Bool.not_true, Bool.false_or, decide_eq_true_eq] at checked
  exact checked

private theorem sequence_from_syn (s : Snapshot) (f : Values)
    (valid : invariantsHold model s = true) (syn : TypedMachine.eval s f e743 = true) :
    TypedMachine.eval s f e763 = TypedMachine.eval s f e493 ∧
    TypedMachine.eval s f e976 = TypedMachine.eval s f e492 := by
  have base := List.all_eq_true.mp valid e1685 (by rw [model_invariants]; simp)
  have synCurrent : TypedMachine.eval s zeroValues e743 = true := syn
  change (!TypedMachine.eval s zeroValues e743 || TypedMachine.eval s zeroValues e1684) = true at base
  simp only [synCurrent, Bool.not_true, Bool.false_or] at base
  have una : TypedMachine.eval s f e976 = TypedMachine.eval s f e492 := of_decide_eq_true base
  have chain : TypedMachine.eval s zeroValues e1674 = true := by
    change (((((false || TypedMachine.eval s zeroValues e743) ||
      TypedMachine.eval s zeroValues e810) || TypedMachine.eval s zeroValues e955) ||
      TypedMachine.eval s zeroValues e962) || TypedMachine.eval s zeroValues e964) = true
    simp [synCurrent]
  have control := List.all_eq_true.mp valid e1679 (by rw [model_invariants]; simp)
  change (!TypedMachine.eval s zeroValues e1674 || TypedMachine.eval s zeroValues e1678) = true at control
  simp only [chain, Bool.not_true, Bool.false_or] at control
  obtain ⟨next, start⟩ := split_ands s zeroValues e1676 e1677 control
  have tx : TypedMachine.eval s f e976 = TypedMachine.eval s f e518 := of_decide_eq_true start
  have nextSeq : TypedMachine.eval s f e763 =
    ValueOps.seqAdd (TypedMachine.eval s f e518) 1 := of_decide_eq_true next
  rw [← tx, una] at nextSeq
  exact ⟨nextSeq, una⟩

private theorem dynamic_checks (s : Snapshot) (f : Values) (kind : OpenKind)
    (valid : invariantsHold model s = true)
    (on : TypedMachine.eval s f (inputPhase kind) = true) :
    Each (fun inv => TypedMachine.eval s f (ExprRewrite.run (reads kind) inv) = true) dynamicClauses := by
  have empty := buffers_empty s f kind valid on
  cases kind
  · refine ⟨rfl, rfl, rfl, ?_, ?_, empty, trivial⟩
    · change (decide (TypedMachine.eval s f e493 = TypedMachine.eval s f e493) &&
        decide (TypedMachine.eval s f e492 = TypedMachine.eval s f e492)) = true
      simp
    · change decide (TypedMachine.eval s f e492 = TypedMachine.eval s f e492) = true
      simp
  · have stopped : TypedMachine.eval s zeroValues e1635 = false :=
      timer_from s e580 e1635 false valid (show e1640 ∈ model.invariants from by rw [model_invariants]; simp) on
    refine ⟨rfl, rfl, ?_, ?_, rfl, empty, trivial⟩
    · exact decide_eq_true stopped
    · change (decide (TypedMachine.eval s f e493 = TypedMachine.eval s f e493) &&
        decide (TypedMachine.eval s f e492 = TypedMachine.eval s f e492)) = true
      simp
  · have stopped : TypedMachine.eval s zeroValues e1635 = false :=
      timer_from s e743 e1635 false valid (show e1645 ∈ model.invariants from by rw [model_invariants]; simp) on
    have retransmit : TypedMachine.eval s zeroValues e1629 = true :=
      timer_from s e743 e1629 true valid (show e1642 ∈ model.invariants from by rw [model_invariants]; simp) on
    have user : TypedMachine.eval s zeroValues e1632 = true :=
      timer_from s e743 e1632 true valid (show e1644 ∈ model.invariants from by rw [model_invariants]; simp) on
    obtain ⟨next, una⟩ := sequence_from_syn s f valid on
    refine ⟨decide_eq_true retransmit, decide_eq_true user, decide_eq_true stopped, ?_, rfl, empty, trivial⟩
    change (decide (TypedMachine.eval s f e763 = TypedMachine.eval s f e493) &&
      decide (TypedMachine.eval s f e976 = TypedMachine.eval s f e492)) = true
    rw [decide_eq_true next, decide_eq_true una]
    rfl

private def post (r : Rule) (kind : OpenKind) (phase : LinkPhase) (inv : Expr .boolean) :=
  (obligationsFor r none [inv]).drop (delays kind phase).length

private theorem tcp_classes (kind : OpenKind) (inv : Expr .boolean)
    (covered : inv ∈ tcpClauses kind) :
    inv ∈ staticClauses kind ∨ inv ∈ dynamicClauses := by
  simp only [tcpClauses, phaseClauses, List.mem_append] at covered
  rcases covered with (((((before | timed) | after) | sequence) | timeout) | rest)
  · exact Or.inl (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ before)))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at timed
    rcases timed with rfl | rfl | rfl <;> exact Or.inr (by simp [dynamicClauses])
  · exact Or.inl (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ after)))
  · have same := List.mem_singleton.mp sequence
    subst inv
    exact Or.inr (by simp [dynamicClauses])
  · exact Or.inl (List.mem_append_left _ (List.mem_append_right _ timeout))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at rest
    rcases rest with rfl | rfl | rfl | rfl | rfl
    · exact Or.inr (by simp [dynamicClauses])
    · exact Or.inl (List.mem_append_right _ (by simp))
    · exact Or.inl (List.mem_append_right _ (by simp))
    · exact Or.inr (by simp [dynamicClauses])
    · exact Or.inl (List.mem_append_right _ (by simp))

private theorem classify (kind : OpenKind) (phase : LinkPhase) (inv : Expr .boolean)
    (covered : inv ∈ affectedOpen kind phase) :
    inv ∈ staticClauses kind ∨ inv ∈ dynamicClauses ∨ inv ∈ linkClauses phase ∨ inv = e1706 := by
  have protocol (covered : inv ∈ tcpClauses kind) :
      inv ∈ staticClauses kind ∨ inv ∈ dynamicClauses ∨ inv ∈ linkClauses phase ∨ inv = e1706 := by
    rcases tcp_classes kind inv covered with static | dynamic
    · exact Or.inl static
    · exact Or.inr (Or.inl dynamic)
  have phaseKnown (equal : inv = e1716) : inv ∈ staticClauses kind := by
    subst inv
    exact List.mem_append_right _ (by simp)
  cases phase
  · simp only [affectedOpen, List.mem_append] at covered
    rcases covered with ((link | tcp) | tail)
    · apply Or.inr; apply Or.inr; apply Or.inl
      simp only [linkClauses, List.mem_cons, List.not_mem_nil, or_false] at link ⊢
      rcases link with a | a | a | a | a | a | a | a <;> simp only [a, true_or, or_true]
    · exact protocol tcp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at tail
      rcases tail with packet | known | owner
      · exact Or.inr (Or.inr (Or.inr packet))
      · exact Or.inl (phaseKnown known)
      · exact Or.inr (Or.inr (Or.inl (by simp [linkClauses, owner])))
  · simp only [affectedOpen, List.mem_append] at covered
    rcases covered with ((link | tcp) | tail)
    · apply Or.inr; apply Or.inr; apply Or.inl
      simp only [linkClauses, List.mem_cons, List.not_mem_nil, or_false] at link ⊢
      rcases link with a | a | a <;> simp only [a, true_or, or_true]
    · exact protocol tcp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at tail
      rcases tail with packet | known | owner
      · exact Or.inr (Or.inr (Or.inr packet))
      · exact Or.inl (phaseKnown known)
      · exact Or.inr (Or.inr (Or.inl (by simp [linkClauses, owner])))
  · simp only [affectedOpen, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at covered
    rcases covered with tcp | packet | known
    · exact protocol tcp
    · exact Or.inr (Or.inr (Or.inr packet))
    · exact Or.inl (phaseKnown known)

private theorem delay_valid (s : Snapshot) (f : Values) (kind : OpenKind) (phase : LinkPhase)
    (valid : invariantsHold model s = true) : holds (delays kind phase) s f = true := by
  have active : 1 ≤ TypedMachine.eval s f e567 :=
    of_decide_eq_true (List.all_eq_true.mp valid e1683 (by rw [model_invariants]; simp))
  cases kind <;> cases phase
  all_goals first | rfl | (change (decide (1 ≤ TypedMachine.eval s f e567) && true) = true; simp [active])

private theorem certify (r : Rule) (kind : OpenKind) (phase : LinkPhase)
    (guard : r.guard = .boolAnd (guardFor kind) (linkGuard phase))
    (timing : obligationsFor r none [] = delays kind phase)
    (catalog : model.invariants.filter (fun inv => !ignoresFiring inv r none) = affectedOpen kind phase)
    (statics : ∀ s f, (staticClauses kind).all (fun inv => holds (post r kind phase inv) s f) = true)
    (dynamic : dynamicClauses.map (post r kind phase) =
      dynamicClauses.map (fun e => [ExprRewrite.run (reads kind) e]))
    (linkReady : linkCondition (post r kind phase) phase)
    (packet : (post r kind phase e1706).all OctetBounds.certifies = true) :
    FiringPreserves model r none := by
  apply preserves_touched
  intro s f valid _ enabled
  rw [guard] at enabled
  obtain ⟨input, link⟩ := split_ands s f _ _ enabled
  have delaysPassed := delay_valid s f kind phase valid
  refine ⟨timing ▸ delaysPassed, ?_⟩
  intro inv member seen
  have covered : inv ∈ affectedOpen kind phase := by
    rw [← catalog]
    exact List.mem_filter.mpr ⟨member, by simp [seen]⟩
  have checked : holds (post r kind phase inv) s f = true := by
    rcases classify kind phase inv covered with static | effect | ethernet | rfl
    · exact List.all_eq_true.mp (statics s f) _ static
    · rw [List.map_inj_left.mp dynamic inv effect]
      change (TypedMachine.eval s f (ExprRewrite.run (reads kind) inv) && true) = true
      simp [(dynamic_checks s f kind valid (guard_phase s f kind input)).of_mem effect]
    · exact (link_checks s f _ phase linkReady link valid).of_mem ethernet
    · exact OctetBounds.all_sound _ (context s f) packet
  rw [obligationsFor_split, timing, holds, List.all_append]
  change (holds (delays kind phase) s f && holds (post r kind phase inv) s f) = true
  simp [delaysPassed, checked]

theorem active_empty : Approved.raw_64_external :=
  certify rule_64 .active .empty rfl rfl rfl (fun _ _ => rfl)
    rfl ⟨⟨by decide +kernel, by decide +kernel, rfl⟩, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩⟩ (by decide +kernel)

theorem active_pending : Approved.raw_65_external :=
  certify rule_65 .active .pending rfl rfl rfl (fun _ _ => rfl)
    rfl ⟨by decide +kernel, by decide +kernel, rfl⟩ (by decide +kernel)

theorem active_resolved : Approved.raw_66_external :=
  certify rule_66 .active .resolved rfl rfl rfl (fun _ _ => rfl)
    rfl trivial (by decide +kernel)

theorem passive_empty : Approved.raw_68_external :=
  certify rule_68 .passive .empty rfl rfl rfl (fun _ _ => rfl)
    rfl ⟨⟨by decide +kernel, by decide +kernel, rfl⟩, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩⟩ (by decide +kernel)

theorem passive_pending : Approved.raw_69_external :=
  certify rule_69 .passive .pending rfl rfl rfl (fun _ _ => rfl)
    rfl ⟨by decide +kernel, by decide +kernel, rfl⟩ (by decide +kernel)

theorem passive_resolved : Approved.raw_70_external :=
  certify rule_70 .passive .resolved rfl rfl rfl (fun _ _ => rfl)
    rfl trivial (by decide +kernel)

theorem simultaneous_empty : Approved.raw_71_external :=
  certify rule_71 .simultaneous .empty rfl rfl rfl (fun _ _ => rfl)
    rfl ⟨⟨by decide +kernel, by decide +kernel, rfl⟩, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩⟩ (by decide +kernel)

theorem simultaneous_pending : Approved.raw_72_external :=
  certify rule_72 .simultaneous .pending rfl rfl rfl (fun _ _ => rfl)
    rfl ⟨by decide +kernel, by decide +kernel, rfl⟩ (by decide +kernel)

theorem simultaneous_resolved : Approved.raw_73_external :=
  certify rule_73 .simultaneous .resolved rfl rfl rfl (fun _ _ => rfl)
    rfl trivial (by decide +kernel)

def firings : List (Rule × Option Nat) :=
  [(rule_64, none), (rule_65, none), (rule_66, none), (rule_68, none), (rule_69, none),
   (rule_70, none), (rule_71, none), (rule_72, none), (rule_73, none)]

theorem checked : Each (fun p => FiringPreserves model p.1 p.2) firings :=
  ⟨active_empty, active_pending, active_resolved, passive_empty, passive_pending,
   passive_resolved, simultaneous_empty, simultaneous_pending, simultaneous_resolved, trivial⟩

private theorem openMember (index : Nat) (r : Rule)
    (selected : model.rules[index]? = some r) (external : r.event ∈ model.externalEvents) :
    (r, none) ∈ rawChecks model declaredTimers :=
  raw_external_member model declaredTimers r (List.mem_iff_getElem?.mpr ⟨index, selected⟩) external

theorem members : Each (fun p => p ∈ rawChecks model declaredTimers) firings :=
  ⟨openMember 64 rule_64 rfl (by decide), openMember 65 rule_65 rfl (by decide),
   openMember 66 rule_66 rfl (by decide), openMember 68 rule_68 rfl (by decide),
   openMember 69 rule_69 rfl (by decide), openMember 70 rule_70 rfl (by decide),
   openMember 71 rule_71 rfl (by decide), openMember 72 rule_72 rfl (by decide),
   openMember 73 rule_73 rfl (by decide), trivial⟩

end TCPIPOpen
