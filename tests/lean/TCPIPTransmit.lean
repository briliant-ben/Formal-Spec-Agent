import TCPIPTransmitFacts
import EffectConditions
import GuardedSuffix
import OctetBounds
import TCPIPSendWire

namespace TCPIPTransmit
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts TCPIPTransmitFacts
open EffectConditions EffectFootprint GuardedSuffix TimedObligations TCPIPSendWire
set_option maxRecDepth 16384

private def rule (first : Bool) : LinkPhase → Rule :=
  match first with
  | true => fun phase => match phase with
    | .empty => rule_241 | .pending => rule_242 | .resolved => rule_243
  | false => fun phase => match phase with
    | .empty => rule_244 | .pending => rule_245 | .resolved => rule_246

private def prefixActions (r : Rule) := r.actions.dropLast
private def cut (r : Rule) : Rule := {r with actions := prefixActions r}

private def delays (first : Bool) (phase : LinkPhase) : List (Expr .boolean) :=
  (match phase with | .empty => [.intGe e10 e44] | _ => []) ++
    (if first then [.intGe e566 e44] else [])

private def timerClauses : List (Expr .boolean) :=
  [e1631, e1638, e1642, e1646, e1651, e1654, e1657, e1660, e1663, e1666]

private def tcpClauses (first : Bool) : List (Expr .boolean) :=
  (if first then timerClauses else []) ++ [e1679, e1687, e1690, e1691, e1698, e1704, e1705]

private def sendOctets : Expr .octets := .slice e924 e1 e1230

private def reads (first : Bool) : ExprRewrite.Rewrite :=
  { varRead := fun kind slot =>
      match kind with
      | .integer => .variable .integer slot
      | .octets =>
        if slot = 41 then .concat e928 sendOctets else
        if slot = 40 then .slice e924 e1230 e925 else .variable .octets slot
      | .sequence => if slot = 29 then .seqAdd e763 e1230 else .variable .sequence slot
      | .boolean => .variable .boolean slot
      | .text => .variable .text slot
    field := fun kind slot => .literal kind (getValue kind zeroValues slot)
    stateIs := fun id => .literal .boolean (decide (0 = id))
    timerActive := fun owner =>
      if owner = 2 && first then .literal .boolean true else .timerActive owner }

private theorem timer_checks (s : Snapshot) (f : Values)
    (established : TypedMachine.eval s f e923 = true) :
    Each (fun inv => TypedMachine.eval s f (ExprRewrite.run (reads true) inv) = true) timerClauses := by
  have state : TypedMachine.eval s f e488 = TypedMachine.eval s f e807 :=
    of_decide_eq_true established
  have others (e : Expr .text) (different : TypedMachine.eval s f e807 ≠ TypedMachine.eval s f e) :
      decide (TypedMachine.eval s f e488 = TypedMachine.eval s f e) = false := by
    simp [state, different]
  have closed : TypedMachine.eval s f e489 = false := others e14
    (by change TypedMachine.eval initial zeroValues e807 ≠ TypedMachine.eval initial zeroValues e14; decide)
  have listening : TypedMachine.eval s f e580 = false := others e579
    (by change TypedMachine.eval initial zeroValues e807 ≠ TypedMachine.eval initial zeroValues e579; decide)
  have passiveClose : TypedMachine.eval s f e959 = false := others e958
    (by change TypedMachine.eval initial zeroValues e807 ≠ TypedMachine.eval initial zeroValues e958; decide)
  have finWait : TypedMachine.eval s f e944 = false := others e943
    (by change TypedMachine.eval initial zeroValues e807 ≠ TypedMachine.eval initial zeroValues e943; decide)
  have timeWait : TypedMachine.eval s f e967 = false := others e966
    (by change TypedMachine.eval initial zeroValues e807 ≠ TypedMachine.eval initial zeroValues e966; decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · change (!TypedMachine.eval s f e489 || _) = true; simp [closed]
  · change (!TypedMachine.eval s f e580 || _) = true; simp [listening]
  · change (!TypedMachine.eval s f e743 || true) = true; simp
  · change (!TypedMachine.eval s f e810 || true) = true; simp
  · change (!TypedMachine.eval s f e955 || true) = true; simp
  · change (!TypedMachine.eval s f e959 || _) = true; simp [passiveClose]
  · change (!TypedMachine.eval s f e944 || _) = true; simp [finWait]
  · change (!TypedMachine.eval s f e962 || true) = true; simp
  · change (!TypedMachine.eval s f e964 || true) = true; simp
  · change (!TypedMachine.eval s f e967 || _) = true; simp [timeWait]

private theorem other_control (s : Snapshot) (f : Values)
    (established : TypedMachine.eval s f e923 = true) :
    TypedMachine.eval s f e1674 = false ∧ TypedMachine.eval s f e1702 = false := by
  have state : s.values.texts 56 = TypedMachine.eval initial zeroValues e807 :=
    of_decide_eq_true established
  simp only [e1674, e1673, e1672, e1671, e1670, e1702, e1701, e1700,
    e743, e810, e955, e962, e964, e944, e959, e967, e488, TypedMachine.eval,
    TypedIR.eval, context, getValue, state]
  exact ⟨rfl, rfl⟩

private theorem append_checked {xs ys : List α} {holds : α → Prop}
    (left : Each holds xs) (right : Each holds ys) : Each holds (xs ++ ys) := by
  induction xs with
  | nil => exact right
  | cons _ _ ih => exact ⟨left.1, ih left.2⟩

private theorem tcp_post (s : Snapshot) (f : Values) (first : Bool)
    (valid : invariantsHold model s = true)
    (enabled : TypedMachine.eval s f (transmitGuard first) = true) :
    Each (fun inv => TypedMachine.eval s f (ExprRewrite.run (reads first) inv) = true)
      (tcpClauses first) := by
  obtain ⟨established, buffered, room⟩ := guardFacts s f first enabled
  obtain ⟨bound, window, positive, sequence⟩ := data_preserves s f valid established buffered room
  obtain ⟨notSyn, notClosed⟩ := other_control s f established
  have activity : TypedMachine.eval s f (ExprRewrite.run (reads first) e1687) = true := by
    have afterPositive : decide (1 ≤ ((afterFlight s f).length : Int)) = true := decide_eq_true positive
    cases first
    · have before := List.all_eq_true.mp valid e1687 (by rw [model_invariants]; simp)
      have est : TypedMachine.eval s zeroValues e923 = true := established
      change (!TypedMachine.eval s zeroValues e923 || TypedMachine.eval s zeroValues e1686) = true at before
      simp only [est, Bool.not_true, Bool.false_or] at before
      have matching : decide (TypedMachine.eval s f e1629 = TypedMachine.eval s f e1243) = true := before
      have active : TypedMachine.eval s f e1629 = true :=
        (of_decide_eq_true matching).trans (continuing_flight s f enabled)
      change (!TypedMachine.eval s f e923 || decide (TypedMachine.eval s f e1629 =
        decide (1 ≤ ((afterFlight s f).length : Int)))) = true
      rw [afterPositive]
      simp [established, active]
    · change (!TypedMachine.eval s f e923 || decide (true =
        decide (1 ≤ ((afterFlight s f).length : Int)))) = true
      rw [afterPositive]
      simp [established]
  have common : Each (fun inv => TypedMachine.eval s f (ExprRewrite.run (reads first) inv) = true)
      [e1679, e1687, e1690, e1691, e1698, e1704, e1705] := by
    refine ⟨?_, activity, ?_, ?_, ?_, ?_, ?_, trivial⟩
    · change (!TypedMachine.eval s f e1674 || _) = true
      simp [notSyn]
    · change (!TypedMachine.eval s f e923 || decide (ValueOps.seqAdd (TypedMachine.eval s f e763)
        (sendCount s f) = ValueOps.seqAdd (TypedMachine.eval s f e976) (afterFlight s f).length)) = true
      simp [established, sequence]
    · exact decide_eq_true bound
    · change (!(!TypedMachine.eval s f e923) || _) = true
      simp [established]
    · change (!TypedMachine.eval s f e1702 || _) = true
      simp [notClosed]
    · exact decide_eq_true window
  cases first
  · exact common
  · exact append_checked (timer_checks s f established) common

private def postChecks (first : Bool) (phase : LinkPhase) (inv : Expr .boolean) : List (Expr .boolean) :=
  (obligationsFor (cut (rule first phase)) none [inv]).drop (delays first phase).length

private abbrev Post (s : Snapshot) (f : Values) (first : Bool) (phase : LinkPhase) (inv : Expr .boolean) : Prop :=
  holds (postChecks first phase inv) s f = true

private theorem tcp_checks (s : Snapshot) (f : Values) (first : Bool) (phase : LinkPhase)
    (align : (tcpClauses first).map (postChecks first phase) =
      (tcpClauses first).map (fun inv => [ExprRewrite.run (reads first) inv]))
    (valid : invariantsHold model s = true) (enabled : TypedMachine.eval s f (transmitGuard first) = true)
    (inv : Expr .boolean) (member : inv ∈ tcpClauses first) : Post s f first phase inv := by
  unfold Post
  rw [List.map_inj_left.mp align inv member]
  change (TypedMachine.eval s f (ExprRewrite.run (reads first) inv) && true) = true
  simp [(tcp_post s f first valid enabled).of_mem member]

set_option maxHeartbeats 1800000 in
private theorem packet_bound (s : Snapshot) (f : Values) (first : Bool) (phase : LinkPhase) :
    Post s f first phase e1706 := by
  apply OctetBounds.all_sound (postChecks first phase e1706) (context s f)
  cases first <;> cases phase <;> decide +kernel

private def queuePacket : Expr .octets :=
  match postChecks true .pending e1612 with
  | [.intLe (.bytesLength packet) _] => packet
  | _ => .literal .octets []

private theorem queue_bound :
    OctetBounds.certifies (.intLe (.bytesLength queuePacket) e244) = true := by decide +kernel

private theorem queue_minimum : 28 ≤ OctetBounds.lower queuePacket := by decide +kernel

set_option maxHeartbeats 1800000 in
private theorem link_checks (s : Snapshot) (f : Values) (first : Bool) (phase : LinkPhase)
    (enabled : TypedMachine.eval s f (linkGuard phase) = true)
    (valid : invariantsHold model s = true) :
    Each (Post s f first phase) (linkClauses phase) := by
  cases phase
  · have aligned : queueClauses.map (postChecks first .empty) =
        (queueChecks queuePacket (.equal .text e34 e34)).map (fun e => [e]) := by
      cases first <;> rfl
    have queued := queue_from_post s f _ _ _ aligned queue_bound queue_minimum rfl
    obtain ⟨mac, noExpiry⟩ := pending_cache_requirements s f enabled valid
    have cache : Post s f first .empty e1597 := by
      cases first <;>
        change (((TypedMachine.eval s f e1587 && true) && TypedMachine.eval s f e1592) && true) = true
      all_goals simp [mac, noExpiry]
    cases first <;> exact ⟨rfl, cache, rfl, rfl, queued.1, queued.2.1, queued.2.2.1, rfl,
      queued.2.2.2.1, trivial⟩
  · have aligned : queueClauses.map (postChecks first .pending) =
        (queueChecks queuePacket e35).map (fun e => [e]) := by
      cases first <;> rfl
    exact queue_from_post s f _ _ _ aligned queue_bound queue_minimum enabled
  · trivial

private theorem positive_delays (s : Snapshot) (f : Values) (first : Bool) (phase : LinkPhase)
    (valid : invariantsHold model s = true) : holds (delays first phase) s f = true := by
  have timeout : 1000 ≤ TypedMachine.eval s f e566 :=
    of_decide_eq_true (List.all_eq_true.mp valid e1680 (by rw [model_invariants]; simp))
  have positive := Int.le_trans (by decide : (1 : Int) ≤ 1000) timeout
  cases first <;> cases phase
  all_goals first | rfl | (change (decide (1 ≤ TypedMachine.eval s f e566) && true) = true; simp [positive])

private theorem certify (first : Bool) (phase : LinkPhase)
    (shape : (rule first phase).guard = .boolAnd (transmitGuard first) (linkGuard phase))
    (actions : (rule first phase).actions = prefixActions (rule first phase) ++ [.assign .text 56 e807])
    (untouched : (prefixActions (rule first phase)).all (ignoresAction (.variable .text 56)) = true)
    (catalog : model.invariants.filter (fun inv => !ignoresFiring inv (cut (rule first phase)) none) =
      affected (tcpClauses first) phase)
    (timing : obligationsFor (cut (rule first phase)) none [] = delays first phase)
    (alignment : (tcpClauses first).map (postChecks first phase) =
      (tcpClauses first).map (fun inv => [ExprRewrite.run (reads first) inv])) :
    FiringPreserves model (rule first phase) none := by
  apply preserves_after_removing_text model _ none (prefixActions (rule first phase)) 56
    (TypedMachine.eval initial zeroValues e807) actions untouched
  · intro s f enabled
    rw [shape] at enabled
    exact of_decide_eq_true (guardFacts s f first (both s f _ _ enabled).1).1
  · change FiringPreserves model (cut (rule first phase)) none
    apply preserves_touched
    intro s f valid _ enabled
    change TypedMachine.eval s f (rule first phase).guard = true at enabled
    rw [shape] at enabled
    obtain ⟨tcp, link⟩ := both s f _ _ enabled
    have time := positive_delays s f first phase valid
    refine ⟨timing ▸ time, ?_⟩
    intro inv member seen
    have included : inv ∈ affected (tcpClauses first) phase := by
      rw [← catalog]
      exact List.mem_filter.mpr ⟨member, by simp [seen]⟩
    have post : Post s f first phase inv := by
      rcases partition phase (tcpClauses first) inv included with tcpMember | linkMember | rfl
      · exact tcp_checks s f first phase alignment valid tcp inv tcpMember
      · exact (link_checks s f first phase link valid).of_mem linkMember
      · exact packet_bound s f first phase
    rw [obligationsFor_split, timing, holds, List.all_append]
    change (holds (delays first phase) s f && holds (postChecks first phase inv) s f) = true
    simp [time, post]

theorem first_empty : Approved.raw_241_external :=
  certify true .empty rfl rfl (by decide +kernel) rfl rfl rfl

theorem first_pending : Approved.raw_242_external :=
  certify true .pending rfl rfl (by decide +kernel) rfl rfl rfl

theorem first_resolved : Approved.raw_243_external :=
  certify true .resolved rfl rfl (by decide +kernel) rfl rfl rfl

theorem continued_empty : Approved.raw_244_external :=
  certify false .empty rfl rfl (by decide +kernel) rfl rfl rfl

theorem continued_pending : Approved.raw_245_external :=
  certify false .pending rfl rfl (by decide +kernel) rfl rfl rfl

theorem continued_resolved : Approved.raw_246_external :=
  certify false .resolved rfl rfl (by decide +kernel) rfl rfl rfl

def firings : List (Rule × Option Nat) :=
  [(rule_241, none), (rule_242, none), (rule_243, none),
   (rule_244, none), (rule_245, none), (rule_246, none)]

theorem checked : Each (fun p => FiringPreserves model p.1 p.2) firings :=
  ⟨first_empty, first_pending, first_resolved, continued_empty, continued_pending,
   continued_resolved, trivial⟩

private theorem transmitMember (index : Nat) (r : Rule)
    (selected : model.rules[index]? = some r) (external : r.event ∈ model.externalEvents) :
    (r, none) ∈ rawChecks model declaredTimers :=
  raw_external_member model declaredTimers r (List.mem_iff_getElem?.mpr ⟨index, selected⟩) external

theorem members : Each (fun p => p ∈ rawChecks model declaredTimers) firings :=
  ⟨transmitMember 241 rule_241 rfl (by decide), transmitMember 242 rule_242 rfl (by decide),
   transmitMember 243 rule_243 rfl (by decide), transmitMember 244 rule_244 rfl (by decide),
   transmitMember 245 rule_245 rfl (by decide), transmitMember 246 rule_246 rfl (by decide), trivial⟩

end TCPIPTransmit
