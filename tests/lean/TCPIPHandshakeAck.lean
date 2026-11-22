import Approved
import TCPIPSendWire

namespace TCPIPHandshakeAck
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts
open EffectConditions EffectFootprint TimedObligations TCPIPSendWire
set_option maxRecDepth 16384

private def phaseBefore : List (Expr .boolean) :=
  [e1631, e1634, e1637, e1638, e1639, e1640, e1642, e1644, e1645, e1646, e1647, e1648, e1649]

private def phaseAfter : List (Expr .boolean) :=
  [e1651, e1652, e1653, e1654, e1655, e1656, e1657, e1658, e1659,
   e1660, e1661, e1662, e1663, e1664, e1665, e1666, e1667, e1669]

private def timeoutClause (changed : Bool) := if changed then [e1680] else []

private def tcpClauses (changed : Bool) : List (Expr .boolean) :=
  phaseBefore ++ [e1650] ++ phaseAfter ++ [e1679] ++ timeoutClause changed ++
    [e1685, e1687, e1690, e1696, e1698, e1704, e1705]

private def staticClauses (changed : Bool) : List (Expr .boolean) :=
  phaseBefore ++ phaseAfter ++ timeoutClause changed ++ [e1679, e1685, e1698, e1704, e1716]

private def dynamicClauses : List (Expr .boolean) := [e1650, e1687, e1690, e1696, e1705]

private def affectedAck (changed : Bool) (link : Option LinkPhase) : List (Expr .boolean) :=
  match link with
  | some .empty => [e1594, e1597, e1601, e1604, e1612, e1614, e1615, e1628] ++
      tcpClauses changed ++ [e1706, e1716, e1721]
  | some .pending => [e1612, e1614, e1615] ++ tcpClauses changed ++ [e1706, e1716, e1721]
  | some .resolved => tcpClauses changed ++ [e1706, e1716]
  | none => tcpClauses changed ++ [e1716]

private def delays : Option LinkPhase → List (Expr .boolean)
  | some .empty => [.intGe e10 e44]
  | _ => []

private def guarded (base : Expr .boolean) (link : Option LinkPhase) : Expr .boolean :=
  match link with
  | none => base
  | some phase => .boolAnd base (linkGuard phase)

private def linkChecks : Option LinkPhase → List (Expr .boolean)
  | none => []
  | some phase => linkClauses phase

private def post (r : Rule) (link : Option LinkPhase) (inv : Expr .boolean) :=
  (obligationsFor r none [inv]).drop (delays link).length

private def reads : ExprRewrite.Rewrite :=
  { varRead := fun k slot =>
      match k with
      | .text => if slot = 56 then e807 else .variable .text slot
      | .sequence => if slot = 28 then e762 else .variable .sequence slot
      | .integer => if slot = 43 then e772 else .variable .integer slot
      | .boolean => .variable .boolean slot
      | .octets => .variable .octets slot
    field := fun k slot => .literal k (getValue k zeroValues slot)
    stateIs := fun id => .literal .boolean (decide (0 = id))
    timerActive := fun id =>
      if id = 2 || id = 4 then .literal .boolean false else .timerActive id }

private theorem both (s : Snapshot) (f : Values) (x y : Expr .boolean)
    (enabled : TypedMachine.eval s f (.boolAnd x y) = true) :
    TypedMachine.eval s f x = true ∧ TypedMachine.eval s f y = true := by
  change (TypedMachine.eval s f x && TypedMachine.eval s f y) = true at enabled
  simpa only [Bool.and_eq_true] using enabled

private abbrev fixedText (e : Expr .text) := TypedMachine.eval initial zeroValues e

private theorem retransmit_empty (s : Snapshot) (f : Values) (start : String)
    (valid : invariantsHold model s = true) (phase : TypedMachine.eval s f e488 = start)
    (other : start ≠ fixedText e807) : TypedMachine.eval s f e929 = 0 := by
  have outside : TypedMachine.eval s zeroValues e923 = false := by
    change decide (TypedMachine.eval s f e488 = fixedText e807) = false
    rw [phase]
    exact decide_eq_false other
  have safe := List.all_eq_true.mp valid e1698 (by rw [model_invariants]; simp)
  change (!(!TypedMachine.eval s zeroValues e923) || TypedMachine.eval s zeroValues e935) = true at safe
  simp only [outside, Bool.not_false, Bool.not_true, Bool.false_or] at safe
  have empty := (both s zeroValues e927 e930 (both s zeroValues e931 e934 safe).1).2
  exact of_decide_eq_true empty

private theorem wait_timer_stopped (s : Snapshot) (f : Values) (source : Expr .boolean)
    (valid : invariantsHold model s = true)
    (member : .implies source e1636 ∈ model.invariants) (phase : TypedMachine.eval s f source = true)
    (same : TypedMachine.eval s zeroValues source = TypedMachine.eval s f source) :
    TypedMachine.eval s f e1635 = false := by
  have check := List.all_eq_true.mp valid _ member
  change (!TypedMachine.eval s zeroValues source || decide (TypedMachine.eval s f e1635 = false)) = true at check
  simp only [same, phase, Bool.not_true, Bool.false_or, decide_eq_true_eq] at check
  exact check

private theorem octet_range (data : Bytes) (offset : Int) :
    0 ≤ byteAt data offset ∧ byteAt data offset ≤ 255 := by
  unfold byteAt
  split
  · decide
  · have finite := (data.getD offset.toNat 0).isLt
    change 0 ≤ ((data.getD offset.toNat 0).val : Int) ∧
      ((data.getD offset.toNat 0).val : Int) ≤ 255
    omega

private theorem window_range (s : Snapshot) (f : Values) :
    0 ≤ TypedMachine.eval s f e772 ∧ TypedMachine.eval s f e772 ≤ 65535 := by
  have combine (hi lo : Int) (h : 0 ≤ hi ∧ hi ≤ 255) (l : 0 ≤ lo ∧ lo ≤ 255) :
      0 ≤ hi * 256 + lo ∧ hi * 256 + lo ≤ 65535 := by omega
  exact combine _ _ (octet_range (TypedMachine.eval s f e583) 34)
    (octet_range (TypedMachine.eval s f e583) 35)

private theorem dynamic_checks (s : Snapshot) (f : Values)
    (stopped : TypedMachine.eval s f e1635 = false)
    (ack : TypedMachine.eval s f e762 = TypedMachine.eval s f e763)
    (empty : TypedMachine.eval s f e929 = 0) :
    Each (fun inv => TypedMachine.eval s f (ExprRewrite.run reads inv) = true) dynamicClauses := by
  have bounds := window_range s f
  refine ⟨?_, ?_, ?_, ?_, ?_, trivial⟩
  · exact decide_eq_true stopped
  · change decide (false = decide (1 ≤ TypedMachine.eval s f e929)) = true
    rw [empty]
    rfl
  · change decide (TypedMachine.eval s f e763 =
      ValueOps.seqAdd (TypedMachine.eval s f e762) (TypedMachine.eval s f e929)) = true
    rw [empty, ack]
    apply decide_eq_true
    apply Fin.ext
    change (TypedMachine.eval s f e763).val =
      ((((TypedMachine.eval s f e763).val : Int) + 0) % 4294967296).toNat % 4294967296
    have bound := (TypedMachine.eval s f e763).isLt
    rw [Int.add_zero, Int.emod_eq_of_lt (by omega) (by omega)]
    simp [Nat.mod_eq_of_lt bound]
  · change ((decide (0 ≤ TypedMachine.eval s f e772)) &&
      decide (TypedMachine.eval s f e772 ≤ 65535)) = true
    rw [decide_eq_true bounds.1, decide_eq_true bounds.2]
    rfl
  · change decide (TypedMachine.eval s f e929 ≤ TypedMachine.eval s f e772) = true
    rw [empty]
    exact decide_eq_true bounds.1

private inductive HandshakeKind where
  | active | passive | simultaneous | activeRetry | passiveRetry | simultaneousRetry | activeMultiple | passiveMultiple | simultaneousMultiple

private def guardFor : HandshakeKind → Expr .boolean
  | .active => e780
  | .passive => e819
  | .simultaneous => e827
  | .activeRetry => e836
  | .passiveRetry => e845
  | .simultaneousRetry => e850
  | .activeMultiple => e859
  | .passiveMultiple => e867
  | .simultaneousMultiple => e872

private def fromSynSent : HandshakeKind → Bool
  | .active | .activeRetry | .activeMultiple => true
  | _ => false

private def source (kind : HandshakeKind) := if fromSynSent kind then e743 else e810
private def sourceText (kind : HandshakeKind) := if fromSynSent kind then e568 else e740
private def adjustsTimeout : HandshakeKind → Bool
  | .activeRetry | .passiveRetry | .simultaneousRetry => true
  | _ => false

private theorem guard_facts (s : Snapshot) (f : Values) (kind : HandshakeKind)
    (enabled : TypedMachine.eval s f (guardFor kind) = true) :
    TypedMachine.eval s f (source kind) = true ∧ TypedMachine.eval s f e764 = true := by
  cases kind
  · have gated := (both s f e779 e721 enabled).1
    refine ⟨(both s f e743 e778 gated).1, ?_⟩
    have checked1 := (both s f e743 e778 gated).2
    have checked2 := (both s f e749 e777 checked1).2
    have checked3 := (both s f e767 e776 checked2).1
    exact (both s f e764 e766 checked3).1
  · have gated := (both s f e818 e721 enabled).1
    refine ⟨(both s f e810 e817 gated).1, ?_⟩
    have checked1 := (both s f e810 e817 gated).2
    have checked2 := (both s f e812 e816 checked1).2
    have checked3 := (both s f e815 e776 checked2).1
    have checked4 := (both s f e814 e766 checked3).1
    exact (both s f e764 e813 checked4).1
  · have gated := (both s f e826 e721 enabled).1
    refine ⟨(both s f e810 e825 gated).1, ?_⟩
    have checked1 := (both s f e810 e825 gated).2
    have checked2 := (both s f e749 e824 checked1).2
    have checked3 := (both s f e823 e776 checked2).1
    have checked4 := (both s f e822 e766 checked3).1
    exact (both s f e764 e821 checked4).1
  · have gated := (both s f e835 e721 enabled).1
    refine ⟨(both s f e743 e834 gated).1, ?_⟩
    have checked1 := (both s f e743 e834 gated).2
    have checked2 := (both s f e749 e833 checked1).2
    have checked3 := (both s f e832 e776 checked2).1
    exact (both s f e764 e831 checked3).1
  · have gated := (both s f e844 e721 enabled).1
    refine ⟨(both s f e810 e843 gated).1, ?_⟩
    have checked1 := (both s f e810 e843 gated).2
    have checked2 := (both s f e812 e842 checked1).2
    have checked3 := (both s f e841 e776 checked2).1
    have checked4 := (both s f e814 e831 checked3).1
    exact (both s f e764 e813 checked4).1
  · have gated := (both s f e849 e721 enabled).1
    refine ⟨(both s f e810 e848 gated).1, ?_⟩
    have checked1 := (both s f e810 e848 gated).2
    have checked2 := (both s f e749 e847 checked1).2
    have checked3 := (both s f e846 e776 checked2).1
    have checked4 := (both s f e822 e831 checked3).1
    exact (both s f e764 e821 checked4).1
  · have gated := (both s f e858 e721 enabled).1
    refine ⟨(both s f e743 e857 gated).1, ?_⟩
    have checked1 := (both s f e743 e857 gated).2
    have checked2 := (both s f e749 e856 checked1).2
    have checked3 := (both s f e855 e776 checked2).1
    exact (both s f e764 e854 checked3).1
  · have gated := (both s f e866 e721 enabled).1
    refine ⟨(both s f e810 e865 gated).1, ?_⟩
    have checked1 := (both s f e810 e865 gated).2
    have checked2 := (both s f e812 e864 checked1).2
    have checked3 := (both s f e863 e776 checked2).1
    have checked4 := (both s f e814 e854 checked3).1
    exact (both s f e764 e813 checked4).1
  · have gated := (both s f e871 e721 enabled).1
    refine ⟨(both s f e810 e870 gated).1, ?_⟩
    have checked1 := (both s f e810 e870 gated).2
    have checked2 := (both s f e749 e869 checked1).2
    have checked3 := (both s f e868 e776 checked2).1
    have checked4 := (both s f e822 e854 checked3).1
    exact (both s f e764 e821 checked4).1

private theorem tcp_classes (changed : Bool) (inv : Expr .boolean)
    (covered : inv ∈ tcpClauses changed) : inv ∈ staticClauses changed ∨ inv ∈ dynamicClauses := by
  simp only [tcpClauses, List.mem_append] at covered
  rcases covered with (((((before | established) | after) | sequence) | timeout) | rest)
  · exact Or.inl (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ before)))
  · obtain rfl := List.mem_singleton.mp established
    exact Or.inr (by simp [dynamicClauses])
  · exact Or.inl (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ after)))
  · obtain rfl := List.mem_singleton.mp sequence
    exact Or.inl (List.mem_append_right _ (by simp))
  · exact Or.inl (List.mem_append_left _ (List.mem_append_right _ timeout))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at rest
    rcases rest with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (List.mem_append_right _ (by simp))
    · exact Or.inr (by simp [dynamicClauses])
    · exact Or.inr (by simp [dynamicClauses])
    · exact Or.inr (by simp [dynamicClauses])
    · exact Or.inl (List.mem_append_right _ (by simp))
    · exact Or.inl (List.mem_append_right _ (by simp))
    · exact Or.inr (by simp [dynamicClauses])

private theorem classify (changed : Bool) (link : Option LinkPhase) (inv : Expr .boolean)
    (covered : inv ∈ affectedAck changed link) :
    inv ∈ staticClauses changed ∨ inv ∈ dynamicClauses ∨ inv ∈ linkChecks link ∨
      (∃ phase, link = some phase ∧ inv = e1706) := by
  have protocol (covered : inv ∈ tcpClauses changed) :
      inv ∈ staticClauses changed ∨ inv ∈ dynamicClauses ∨ inv ∈ linkChecks link ∨
        (∃ phase, link = some phase ∧ inv = e1706) := by
    rcases tcp_classes changed inv covered with static | dynamic
    · exact Or.inl static
    · exact Or.inr (Or.inl dynamic)
  have phaseKnown (equal : inv = e1716) : inv ∈ staticClauses changed := by
    subst inv
    exact List.mem_append_right _ (by simp)
  cases link with
  | none =>
    rcases List.mem_append.mp covered with tcp | known
    · exact protocol tcp
    · exact Or.inl (phaseKnown (List.mem_singleton.mp known))
  | some phase =>
    cases phase
    · simp only [affectedAck, List.mem_append] at covered
      rcases covered with ((link | tcp) | tail)
      · apply Or.inr; apply Or.inr; apply Or.inl
        simp only [linkChecks, linkClauses, List.mem_cons, List.not_mem_nil, or_false] at link ⊢
        rcases link with a | a | a | a | a | a | a | a <;> simp only [a, true_or, or_true]
      · exact protocol tcp
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at tail
        rcases tail with packet | known | owner
        · exact Or.inr (Or.inr (Or.inr ⟨.empty, rfl, packet⟩))
        · exact Or.inl (phaseKnown known)
        · exact Or.inr (Or.inr (Or.inl (by simp [linkChecks, linkClauses, owner])))
    · simp only [affectedAck, List.mem_append] at covered
      rcases covered with ((link | tcp) | tail)
      · apply Or.inr; apply Or.inr; apply Or.inl
        simp only [linkChecks, linkClauses, List.mem_cons, List.not_mem_nil, or_false] at link ⊢
        rcases link with a | a | a <;> simp only [a, true_or, or_true]
      · exact protocol tcp
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at tail
        rcases tail with packet | known | owner
        · exact Or.inr (Or.inr (Or.inr ⟨.pending, rfl, packet⟩))
        · exact Or.inl (phaseKnown known)
        · exact Or.inr (Or.inr (Or.inl (by simp [linkChecks, linkClauses, owner])))
    · simp only [affectedAck, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at covered
      rcases covered with tcp | packet | known
      · exact protocol tcp
      · exact Or.inr (Or.inr (Or.inr ⟨.resolved, rfl, packet⟩))
      · exact Or.inl (phaseKnown known)

private def LinkReady (r : Rule) (link : Option LinkPhase) : Prop :=
  match link with
  | none => True
  | some phase => linkCondition (post r link) phase ∧ (post r link e1706).all OctetBounds.certifies = true

private theorem validate_link (r : Rule) (s : Snapshot) (f : Values)
    (base : Expr .boolean) (link : Option LinkPhase) (inv : Expr .boolean)
    (enabled : TypedMachine.eval s f (guarded base link) = true)
    (valid : invariantsHold model s = true) (ready : LinkReady r link)
    (covered : inv ∈ linkChecks link ∨ (∃ phase, link = some phase ∧ inv = e1706)) :
    holds (post r link inv) s f = true := by
  cases link with
  | none =>
    rcases covered with mem | ⟨_, impossible, _⟩
    · exact False.elim (List.not_mem_nil mem)
    · contradiction
  | some phase =>
    rcases covered with mem | ⟨_, _, rfl⟩
    · exact (link_checks s f _ phase ready.1 (both s f base (linkGuard phase) enabled).2 valid).of_mem mem
    · exact OctetBounds.all_sound _ (context s f) ready.2

private theorem certify (r : Rule) (kind : HandshakeKind) (link : Option LinkPhase)
    (guard : r.guard = guarded (guardFor kind) link)
    (timing : obligationsFor r none [] = delays link)
    (catalog : model.invariants.filter (fun inv => !ignoresFiring inv r none) =
      affectedAck (adjustsTimeout kind) link)
    (statics : ∀ s f, (staticClauses (adjustsTimeout kind)).all (fun inv => holds (post r link inv) s f) = true)
    (dynamic : dynamicClauses.map (post r link) = dynamicClauses.map (fun e => [ExprRewrite.run reads e]))
    (ready : LinkReady r link) :
    FiringPreserves model r none := by
  apply preserves_touched
  intro s f valid _ enabled
  rw [guard] at enabled
  have base : TypedMachine.eval s f (guardFor kind) = true := by
    cases link with
    | none => exact enabled
    | some phase => exact (both s f _ (linkGuard phase) enabled).1
  have delaysPassed : holds (delays link) s f = true := by
    cases link with
    | none => rfl
    | some phase => cases phase <;> rfl
  refine ⟨timing ▸ delaysPassed, ?_⟩
  intro inv member seen
  have covered : inv ∈ affectedAck (adjustsTimeout kind) link := by
    rw [← catalog]
    exact List.mem_filter.mpr ⟨member, by simp [seen]⟩
  have checked : holds (post r link inv) s f = true := by
    rcases classify (adjustsTimeout kind) link inv covered with static | effect | ethernet
    · exact List.all_eq_true.mp (statics s f) _ static
    · rw [List.map_inj_left.mp dynamic inv effect]
      obtain ⟨phase, ack⟩ := guard_facts s f kind base
      have phaseName : TypedMachine.eval s f e488 = fixedText (sourceText kind) := by
        cases kind <;> exact of_decide_eq_true phase
      have different : fixedText (sourceText kind) ≠ fixedText e807 := by cases kind <;> decide
      have member : .implies (source kind) e1636 ∈ model.invariants := by
        have sent : e1645 ∈ model.invariants := by rw [model_invariants]; simp
        have received : e1648 ∈ model.invariants := by rw [model_invariants]; simp
        cases kind <;> first | exact sent | exact received
      have same : TypedMachine.eval s zeroValues (source kind) = TypedMachine.eval s f (source kind) := by
        cases kind <;> rfl
      have stopped := wait_timer_stopped s f _ valid member phase same
      have empty := retransmit_empty s f _ valid phaseName different
      change (TypedMachine.eval s f (ExprRewrite.run reads inv) && true) = true
      simp [(dynamic_checks s f stopped (of_decide_eq_true ack) empty).of_mem effect]
    · exact validate_link r s f _ link inv enabled valid ready ethernet
  rw [obligationsFor_split, timing, holds, List.all_append]
  change (holds (delays link) s f && holds (post r link inv) s f) = true
  simp [delaysPassed, checked]

theorem active_empty : Approved.raw_74_external :=
  certify rule_74 .active (some .empty) rfl rfl rfl (fun _ _ => rfl) rfl
    ⟨⟨⟨by decide +kernel, by decide +kernel, rfl⟩, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩⟩,
      by decide +kernel⟩

theorem active_pending : Approved.raw_75_external :=
  certify rule_75 .active (some .pending) rfl rfl rfl (fun _ _ => rfl) rfl
    ⟨⟨by decide +kernel, by decide +kernel, rfl⟩, by decide +kernel⟩

theorem active_resolved : Approved.raw_76_external :=
  certify rule_76 .active (some .resolved) rfl rfl rfl (fun _ _ => rfl) rfl
    ⟨trivial, by decide +kernel⟩

theorem passive : Approved.raw_77_external :=
  certify rule_77 .passive none rfl rfl rfl (fun _ _ => rfl) rfl
    trivial

theorem simultaneous_empty : Approved.raw_78_external :=
  certify rule_78 .simultaneous (some .empty) rfl rfl rfl (fun _ _ => rfl) rfl
    ⟨⟨⟨by decide +kernel, by decide +kernel, rfl⟩, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩⟩,
      by decide +kernel⟩

theorem simultaneous_pending : Approved.raw_79_external :=
  certify rule_79 .simultaneous (some .pending) rfl rfl rfl (fun _ _ => rfl) rfl
    ⟨⟨by decide +kernel, by decide +kernel, rfl⟩, by decide +kernel⟩

theorem simultaneous_resolved : Approved.raw_80_external :=
  certify rule_80 .simultaneous (some .resolved) rfl rfl rfl (fun _ _ => rfl) rfl
    ⟨trivial, by decide +kernel⟩

theorem active_retry_empty : Approved.raw_81_external :=
  certify rule_81 .activeRetry (some .empty) rfl rfl rfl (fun _ _ => rfl) rfl
    ⟨⟨⟨by decide +kernel, by decide +kernel, rfl⟩, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩⟩,
      by decide +kernel⟩

theorem active_retry_pending : Approved.raw_82_external :=
  certify rule_82 .activeRetry (some .pending) rfl rfl rfl (fun _ _ => rfl) rfl
    ⟨⟨by decide +kernel, by decide +kernel, rfl⟩, by decide +kernel⟩

theorem active_retry_resolved : Approved.raw_83_external :=
  certify rule_83 .activeRetry (some .resolved) rfl rfl rfl (fun _ _ => rfl) rfl
    ⟨trivial, by decide +kernel⟩

theorem passive_retry : Approved.raw_84_external :=
  certify rule_84 .passiveRetry none rfl rfl rfl (fun _ _ => rfl) rfl
    trivial

theorem simultaneous_retry_empty : Approved.raw_85_external :=
  certify rule_85 .simultaneousRetry (some .empty) rfl rfl rfl (fun _ _ => rfl) rfl
    ⟨⟨⟨by decide +kernel, by decide +kernel, rfl⟩, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩⟩,
      by decide +kernel⟩

theorem simultaneous_retry_pending : Approved.raw_86_external :=
  certify rule_86 .simultaneousRetry (some .pending) rfl rfl rfl (fun _ _ => rfl) rfl
    ⟨⟨by decide +kernel, by decide +kernel, rfl⟩, by decide +kernel⟩

theorem simultaneous_retry_resolved : Approved.raw_87_external :=
  certify rule_87 .simultaneousRetry (some .resolved) rfl rfl rfl (fun _ _ => rfl) rfl
    ⟨trivial, by decide +kernel⟩

theorem active_multiple_empty : Approved.raw_88_external :=
  certify rule_88 .activeMultiple (some .empty) rfl rfl rfl (fun _ _ => rfl) rfl
    ⟨⟨⟨by decide +kernel, by decide +kernel, rfl⟩, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩⟩,
      by decide +kernel⟩

theorem active_multiple_pending : Approved.raw_89_external :=
  certify rule_89 .activeMultiple (some .pending) rfl rfl rfl (fun _ _ => rfl) rfl
    ⟨⟨by decide +kernel, by decide +kernel, rfl⟩, by decide +kernel⟩

theorem active_multiple_resolved : Approved.raw_90_external :=
  certify rule_90 .activeMultiple (some .resolved) rfl rfl rfl (fun _ _ => rfl) rfl
    ⟨trivial, by decide +kernel⟩

theorem passive_multiple : Approved.raw_91_external :=
  certify rule_91 .passiveMultiple none rfl rfl rfl (fun _ _ => rfl) rfl
    trivial

theorem simultaneous_multiple_empty : Approved.raw_92_external :=
  certify rule_92 .simultaneousMultiple (some .empty) rfl rfl rfl (fun _ _ => rfl) rfl
    ⟨⟨⟨by decide +kernel, by decide +kernel, rfl⟩, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩⟩,
      by decide +kernel⟩

theorem simultaneous_multiple_pending : Approved.raw_93_external :=
  certify rule_93 .simultaneousMultiple (some .pending) rfl rfl rfl (fun _ _ => rfl) rfl
    ⟨⟨by decide +kernel, by decide +kernel, rfl⟩, by decide +kernel⟩

theorem simultaneous_multiple_resolved : Approved.raw_94_external :=
  certify rule_94 .simultaneousMultiple (some .resolved) rfl rfl rfl (fun _ _ => rfl) rfl
    ⟨trivial, by decide +kernel⟩

def firings : List (Rule × Option Nat) :=
  [(rule_74, none), (rule_75, none), (rule_76, none), (rule_77, none), (rule_78, none), (rule_79, none),
   (rule_80, none), (rule_81, none), (rule_82, none), (rule_83, none), (rule_84, none), (rule_85, none),
   (rule_86, none), (rule_87, none), (rule_88, none), (rule_89, none), (rule_90, none), (rule_91, none),
   (rule_92, none), (rule_93, none), (rule_94, none)]

theorem checked : Each (fun p => FiringPreserves model p.1 p.2) firings :=
  ⟨active_empty, active_pending, active_resolved, passive, simultaneous_empty, simultaneous_pending,
   simultaneous_resolved, active_retry_empty, active_retry_pending, active_retry_resolved,
   passive_retry, simultaneous_retry_empty, simultaneous_retry_pending, simultaneous_retry_resolved,
   active_multiple_empty, active_multiple_pending, active_multiple_resolved, passive_multiple,
   simultaneous_multiple_empty, simultaneous_multiple_pending, simultaneous_multiple_resolved, trivial⟩

private theorem external_member (index : Nat) (r : Rule)
    (selected : model.rules[index]? = some r) (external : r.event ∈ model.externalEvents) :
    (r, none) ∈ rawChecks model declaredTimers :=
  raw_external_member model declaredTimers r (List.mem_iff_getElem?.mpr ⟨index, selected⟩) external

theorem members : Each (fun p => p ∈ rawChecks model declaredTimers) firings :=
  ⟨external_member 74 rule_74 rfl (by decide), external_member 75 rule_75 rfl (by decide),
   external_member 76 rule_76 rfl (by decide), external_member 77 rule_77 rfl (by decide),
   external_member 78 rule_78 rfl (by decide), external_member 79 rule_79 rfl (by decide),
   external_member 80 rule_80 rfl (by decide), external_member 81 rule_81 rfl (by decide),
   external_member 82 rule_82 rfl (by decide), external_member 83 rule_83 rfl (by decide),
   external_member 84 rule_84 rfl (by decide), external_member 85 rule_85 rfl (by decide),
   external_member 86 rule_86 rfl (by decide), external_member 87 rule_87 rfl (by decide),
   external_member 88 rule_88 rfl (by decide), external_member 89 rule_89 rfl (by decide),
   external_member 90 rule_90 rfl (by decide), external_member 91 rule_91 rfl (by decide),
   external_member 92 rule_92 rfl (by decide), external_member 93 rule_93 rfl (by decide),
   external_member 94 rule_94 rfl (by decide), trivial⟩

end TCPIPHandshakeAck
