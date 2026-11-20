import Approved
import EffectConditions
import GuardedSuffix
import OctetBounds
import TCPIPSendWire

namespace TCPIPRetransmit
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts
open EffectConditions EffectFootprint GuardedSuffix TimedObligations TCPIPSendWire
set_option maxRecDepth 16384

private def rule : LinkPhase → Rule
  | .empty => rule_258 | .pending => rule_259 | .resolved => rule_260

private def prefixActions (r : Rule) := r.actions.dropLast
private def cut (r : Rule) : Rule := {r with actions := prefixActions r}

private theorem both (s : Snapshot) (f : Values) (x y : Expr .boolean)
    (enabled : TypedMachine.eval s f (.boolAnd x y) = true) :
    TypedMachine.eval s f x = true ∧ TypedMachine.eval s f y = true := by
  change (TypedMachine.eval s f x && TypedMachine.eval s f y) = true at enabled
  simpa only [Bool.and_eq_true] using enabled

private def delays : LinkPhase → List (Expr .boolean)
  | .empty => [.intGe e10 e44, .intGe e1045 e44]
  | _ => [.intGe e1045 e44]

private def tcpClauses : List (Expr .boolean) :=
  [e1631, e1638, e1642, e1646, e1651, e1654, e1657, e1660, e1663, e1666,
   e1680, e1681, e1687]

private def reads : ExprRewrite.Rewrite :=
  { varRead := fun kind slot =>
      match kind with
      | .integer => if slot = 34 then e1045 else if slot = 35 then e1044 else .variable .integer slot
      | .octets => .variable .octets slot
      | .sequence => .variable .sequence slot
      | .boolean => .variable .boolean slot
      | .text => .variable .text slot
    field := fun kind slot => .literal kind (getValue kind zeroValues slot)
    stateIs := fun id => .literal .boolean (decide (0 = id))
    timerActive := fun owner => if owner = 2 then .literal .boolean true else .timerActive owner }

private theorem invariant (s : Snapshot) (e : Expr .boolean)
    (member : e ∈ model.invariants) (valid : invariantsHold model s = true) :
    TypedMachine.eval s zeroValues e = true :=
  List.all_eq_true.mp valid e member

private structure Backoff (s : Snapshot) (f : Values) : Prop where
  timeout : 1000 ≤ TypedMachine.eval s f e1045
  retries : 0 ≤ TypedMachine.eval s f e1044

private theorem backoff (s : Snapshot) (f : Values)
    (valid : invariantsHold model s = true) : Backoff s f := by
  have timeout : 1000 ≤ TypedMachine.eval s f e566 :=
    of_decide_eq_true (invariant s e1680 (by rw [model_invariants]; simp) valid)
  have retries : 0 ≤ TypedMachine.eval s f e765 :=
    of_decide_eq_true (invariant s e1681 (by rw [model_invariants]; simp) valid)
  have doubled (n : Int) (h : 1000 ≤ n) : 1000 ≤ n * 2 := by omega
  have incremented (n : Int) (h : 0 ≤ n) : 0 ≤ n + 1 := by omega
  exact ⟨doubled _ timeout, incremented _ retries⟩

private theorem positive_delays (s : Snapshot) (f : Values) (phase : LinkPhase)
    (facts : Backoff s f) : holds (delays phase) s f = true := by
  have positive : 1 ≤ TypedMachine.eval s f e1045 :=
    Int.le_trans (by decide : (1 : Int) ≤ 1000) facts.timeout
  cases phase <;> change (decide (1 ≤ TypedMachine.eval s f e1045) && true) = true <;>
    simp [positive]

-- These phases require a stopped retransmission timer. The enabled rule
-- already fixes the TCP phase to ESTABLISHED, so their antecedents are false.
private theorem other_phase (s : Snapshot) (f : Values) (value : String)
    (different : TypedMachine.eval s f e807 ≠ value)
    (established : TypedMachine.eval s f e923 = true) :
    decide (TypedMachine.eval s f e488 = value) = false := by
  have phase : TypedMachine.eval s f e488 = TypedMachine.eval s f e807 :=
    of_decide_eq_true established
  simp [phase, different]

private theorem tcp_post (s : Snapshot) (f : Values)
    (established : TypedMachine.eval s f e923 = true)
    (flight : TypedMachine.eval s f e1243 = true)
    (facts : Backoff s f) :
    Each (fun inv => TypedMachine.eval s f (ExprRewrite.run reads inv) = true) tcpClauses := by
  have closed : TypedMachine.eval s f e489 = false :=
    other_phase s f _ (by change TypedMachine.eval initial zeroValues e807 ≠ TypedMachine.eval initial zeroValues e14; decide) established
  have listening : TypedMachine.eval s f e580 = false :=
    other_phase s f _ (by change TypedMachine.eval initial zeroValues e807 ≠ TypedMachine.eval initial zeroValues e579; decide) established
  have passiveClose : TypedMachine.eval s f e959 = false :=
    other_phase s f _ (by change TypedMachine.eval initial zeroValues e807 ≠ TypedMachine.eval initial zeroValues e958; decide) established
  have finWait : TypedMachine.eval s f e944 = false :=
    other_phase s f _ (by change TypedMachine.eval initial zeroValues e807 ≠ TypedMachine.eval initial zeroValues e943; decide) established
  have timeWait : TypedMachine.eval s f e967 = false :=
    other_phase s f _ (by change TypedMachine.eval initial zeroValues e807 ≠ TypedMachine.eval initial zeroValues e966; decide) established
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · change (!TypedMachine.eval s f e489 || _) = true
    simp [closed]
  · change (!TypedMachine.eval s f e580 || _) = true
    simp [listening]
  · change (!TypedMachine.eval s f e743 || true) = true
    simp
  · change (!TypedMachine.eval s f e810 || true) = true
    simp
  · change (!TypedMachine.eval s f e955 || true) = true
    simp
  · change (!TypedMachine.eval s f e959 || _) = true
    simp [passiveClose]
  · change (!TypedMachine.eval s f e944 || _) = true
    simp [finWait]
  · change (!TypedMachine.eval s f e962 || true) = true
    simp
  · change (!TypedMachine.eval s f e964 || true) = true
    simp
  · change (!TypedMachine.eval s f e967 || _) = true
    simp [timeWait]
  · exact decide_eq_true facts.timeout
  · exact decide_eq_true facts.retries
  · change (!TypedMachine.eval s f e923 || decide (true = TypedMachine.eval s f e1243)) = true
    simp [flight]

private def postChecks (phase : LinkPhase) (inv : Expr .boolean) : List (Expr .boolean) :=
  (obligationsFor (cut (rule phase)) (some 2) [inv]).drop (delays phase).length

private abbrev Post (s : Snapshot) (f : Values) (phase : LinkPhase) (inv : Expr .boolean) : Prop :=
  holds (postChecks phase inv) s f = true

private theorem tcp_checks (s : Snapshot) (f : Values) (phase : LinkPhase)
    (align : tcpClauses.map (postChecks phase) =
      tcpClauses.map (fun inv => [ExprRewrite.run reads inv]))
    (established : TypedMachine.eval s f e923 = true)
    (flight : TypedMachine.eval s f e1243 = true) (facts : Backoff s f)
    (inv : Expr .boolean) (member : inv ∈ tcpClauses) :
    Post s f phase inv := by
  unfold Post
  rw [List.map_inj_left.mp align inv member]
  change (TypedMachine.eval s f (ExprRewrite.run reads inv) && true) = true
  simp [(tcp_post s f established flight facts).of_mem member]

set_option maxHeartbeats 1800000 in
private theorem packet_bound (s : Snapshot) (f : Values) (phase : LinkPhase) :
    Post s f phase e1706 := by
  apply OctetBounds.all_sound (postChecks phase e1706) (context s f)
  cases phase <;> decide +kernel

private def queuePacket : Expr .octets :=
  match postChecks .pending e1612 with
  | [.intLe (.bytesLength packet) _] => packet
  | _ => .literal .octets []

private theorem queue_bound :
    OctetBounds.certifies (.intLe (.bytesLength queuePacket) e244) = true := by decide +kernel

private theorem queue_minimum : 28 ≤ OctetBounds.lower queuePacket := by decide +kernel

set_option maxHeartbeats 1800000 in
private theorem link_checks (s : Snapshot) (f : Values) (phase : LinkPhase)
    (enabled : TypedMachine.eval s f (linkGuard phase) = true)
    (valid : invariantsHold model s = true) :
    Each (Post s f phase) (linkClauses phase) := by
  cases phase
  · have aligned : queueClauses.map (postChecks .empty) =
        (queueChecks queuePacket (.equal .text e34 e34)).map (fun e => [e]) := by
      rfl
    have queued := queue_from_post s f _ _ _ aligned queue_bound queue_minimum rfl
    obtain ⟨mac, noExpiry⟩ := pending_cache_requirements s f enabled valid
    have cache : Post s f .empty e1597 := by
      change (((TypedMachine.eval s f e1587 && true) && TypedMachine.eval s f e1592) && true) = true
      simp [mac, noExpiry]
    exact ⟨rfl, cache, rfl, rfl, queued.1, queued.2.1, queued.2.2.1, rfl,
      queued.2.2.2.1, trivial⟩
  · have aligned : queueClauses.map (postChecks .pending) =
        (queueChecks queuePacket e35).map (fun e => [e]) := by
      rfl
    exact queue_from_post s f _ _ _ aligned queue_bound queue_minimum enabled
  · trivial

private theorem certify (phase : LinkPhase)
    (shape : (rule phase).guard = .boolAnd e1328 (linkGuard phase))
    (actions : (rule phase).actions = prefixActions (rule phase) ++ [.assign .text 56 e807])
    (untouched : (prefixActions (rule phase)).all (ignoresAction (.variable .text 56)) = true)
    (catalog : model.invariants.filter (fun inv => !ignoresFiring inv (cut (rule phase)) (some 2)) =
      affected tcpClauses phase)
    (timing : obligationsFor (cut (rule phase)) (some 2) [] = delays phase)
    (alignment : tcpClauses.map (postChecks phase) =
      tcpClauses.map (fun inv => [ExprRewrite.run reads inv])) :
    FiringPreserves model (rule phase) (some 2) := by
  apply preserves_after_removing_text model _ (some 2) (prefixActions (rule phase)) 56
    (TypedMachine.eval initial zeroValues e807) actions untouched
  · intro s f enabled
    rw [shape] at enabled
    exact of_decide_eq_true (both s f e923 e1243 (both s f _ _ enabled).1).1
  · change FiringPreserves model (cut (rule phase)) (some 2)
    apply preserves_touched
    intro s f valid _ enabled
    change TypedMachine.eval s f (rule phase).guard = true at enabled
    rw [shape] at enabled
    obtain ⟨tcp, link⟩ := both s f _ _ enabled
    obtain ⟨established, flight⟩ := both s f e923 e1243 tcp
    have facts := backoff s f valid
    have time := positive_delays s f phase facts
    refine ⟨timing ▸ time, ?_⟩
    intro inv member seen
    have included : inv ∈ affected tcpClauses phase := by
      rw [← catalog]
      exact List.mem_filter.mpr ⟨member, by simp [seen]⟩
    have post : Post s f phase inv := by
      rcases partition phase tcpClauses inv included with tcpMember | linkMember | rfl
      · exact tcp_checks s f phase alignment established flight facts inv tcpMember
      · exact (link_checks s f phase link valid).of_mem linkMember
      · exact packet_bound s f phase
    rw [obligationsFor_split, timing, holds, List.all_append]
    change (holds (delays phase) s f && holds (postChecks phase inv) s f) = true
    simp [time, post]

theorem retransmit_empty : Approved.raw_258_timer_2 :=
  certify .empty rfl rfl (by decide +kernel) rfl rfl rfl

theorem retransmit_pending : Approved.raw_259_timer_2 :=
  certify .pending rfl rfl (by decide +kernel) rfl rfl rfl

theorem retransmit_resolved : Approved.raw_260_timer_2 :=
  certify .resolved rfl rfl (by decide +kernel) rfl rfl rfl

def firings : List (Rule × Option Nat) :=
  [(rule_258, some 2), (rule_259, some 2), (rule_260, some 2)]

theorem checked : Each (fun p => FiringPreserves model p.1 p.2) firings :=
  ⟨retransmit_empty, retransmit_pending, retransmit_resolved, trivial⟩

private theorem timerMember (index : Nat) (r : Rule)
    (selected : model.rules[index]? = some r) (trigger : r.event = model.timerEvents 2) :
    (r, some 2) ∈ rawChecks model declaredTimers :=
  raw_timer_member model declaredTimers r 2 (List.mem_iff_getElem?.mpr ⟨index, selected⟩)
    (by decide) trigger

theorem members : Each (fun p => p ∈ rawChecks model declaredTimers) firings :=
  ⟨timerMember 258 rule_258 rfl rfl, timerMember 259 rule_259 rfl rfl,
    timerMember 260 rule_260 rfl rfl, trivial⟩

end TCPIPRetransmit
