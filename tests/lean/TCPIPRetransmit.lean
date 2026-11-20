import Approved
import EffectConditions
import GuardedSuffix
import OctetBounds
import TCPIPSendWire

namespace TCPIPRetransmit
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts
open EffectConditions EffectFootprint GuardedSuffix TimedObligations TCPIPSendWire
set_option maxRecDepth 16384

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

private abbrev fixedText (e : Expr .text) := TypedMachine.eval initial zeroValues e

private def ArmedPhase (phase : String) : Prop :=
  phase ≠ fixedText e14 ∧ phase ≠ fixedText e579 ∧ phase ≠ fixedText e958 ∧
    phase ≠ fixedText e943 ∧ phase ≠ fixedText e966

private theorem tcp_post (s : Snapshot) (f : Values) (phase : String)
    (current : TypedMachine.eval s f e488 = phase)
    (armed : ArmedPhase phase)
    (flight : phase = fixedText e807 → TypedMachine.eval s f e1243 = true)
    (facts : Backoff s f) :
    Each (fun inv => TypedMachine.eval s f (ExprRewrite.run reads inv) = true) tcpClauses := by
  have other (p : String) (different : phase ≠ p) :
      decide (TypedMachine.eval s f e488 = p) = false := by
    rw [current]
    exact decide_eq_false different
  have closed : TypedMachine.eval s f e489 = false := other _ armed.1
  have listening : TypedMachine.eval s f e580 = false := other _ armed.2.1
  have passiveClose : TypedMachine.eval s f e959 = false := other _ armed.2.2.1
  have finWait : TypedMachine.eval s f e944 = false := other _ armed.2.2.2.1
  have timeWait : TypedMachine.eval s f e967 = false := other _ armed.2.2.2.2
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
    cases phaseGuard : TypedMachine.eval s f e923
    · rfl
    · have isEstablished : phase = fixedText e807 := current.symm.trans (of_decide_eq_true phaseGuard)
      simp [flight isEstablished]

private def postChecks (r : Rule) (phase : LinkPhase) (inv : Expr .boolean) : List (Expr .boolean) :=
  (obligationsFor (cut r) (some 2) [inv]).drop (delays phase).length

private def queuePacket (r : Rule) (phase : LinkPhase) : Expr .octets :=
  match postChecks r phase e1612 with
  | [.intLe (.bytesLength packet) _] => packet
  | _ => .literal .octets []

private def queueCondition (r : Rule) (phase : LinkPhase) (pending : Expr .boolean) : Prop :=
  let packet := queuePacket r phase
  OctetBounds.certifies (.intLe (.bytesLength packet) e244) = true ∧
    28 ≤ OctetBounds.lower packet ∧
    queueClauses.map (postChecks r phase) = (queueChecks packet pending).map (fun e => [e])

private def pendingGuard := Expr.equal .text e34 e34
private def cacheCheck :=
  Expr.implies pendingGuard (.boolAnd (.boolAnd e1587 e3) e1592)

private def linkCondition (r : Rule) (phase : LinkPhase) : Prop :=
  match phase with
  | .empty =>
    queueCondition r .empty pendingGuard ∧
      postChecks r .empty e1597 = [cacheCheck] ∧
      ∀ s f, Each (fun inv => holds (postChecks r .empty inv) s f = true) [e1594, e1601, e1604, e1628]
  | .pending => queueCondition r .pending e35
  | .resolved => True

private theorem link_checks (s : Snapshot) (f : Values) (r : Rule) (phase : LinkPhase)
    (ready : linkCondition r phase) (enabled : TypedMachine.eval s f (linkGuard phase) = true)
    (valid : invariantsHold model s = true) :
    Each (fun inv => holds (postChecks r phase inv) s f = true) (linkClauses phase) := by
  cases phase
  · obtain ⟨⟨bound, min, align⟩, cacheShape, static⟩ := ready
    have queued := queue_from_post s f _ _ _ align bound min rfl
    obtain ⟨mac, noExpiry⟩ := pending_cache_requirements s f enabled valid
    have cache : holds (postChecks r .empty e1597) s f = true := by
      rw [cacheShape]
      change (((TypedMachine.eval s f e1587 && true) && TypedMachine.eval s f e1592) && true) = true
      simp [mac, noExpiry]
    have facts := static s f
    exact ⟨facts.1, cache, facts.2.1, facts.2.2.1, queued.1, queued.2.1, queued.2.2.1,
      facts.2.2.2.1, queued.2.2.2.1, trivial⟩
  · obtain ⟨bound, min, align⟩ := ready
    exact queue_from_post s f _ _ _ align bound min enabled
  · trivial

private theorem certify (r : Rule) (phase : LinkPhase) (tcpGuard : Expr .boolean) (tcpState : String)
    (shape : r.guard = .boolAnd tcpGuard (linkGuard phase))
    (phaseKnown : ∀ s f, TypedMachine.eval s f tcpGuard = true → TypedMachine.eval s f e488 = tcpState)
    (flight : ∀ s f, TypedMachine.eval s f tcpGuard = true →
       tcpState = fixedText e807 → TypedMachine.eval s f e1243 = true)
    (armed : ArmedPhase tcpState)
    (actions : r.actions = prefixActions r ++ [.assign .text 56 (.literal .text tcpState)])
    (untouched : (prefixActions r).all (ignoresAction (.variable .text 56)) = true)
    (catalog : model.invariants.filter (fun inv => !ignoresFiring inv (cut r) (some 2)) =
      affected tcpClauses phase)
    (timing : obligationsFor (cut r) (some 2) [] = delays phase)
    (alignment : tcpClauses.map (postChecks r phase) =
      tcpClauses.map (fun inv => [ExprRewrite.run reads inv]))
    (linkReady : linkCondition r phase)
    (packetBound : (postChecks r phase e1706).all OctetBounds.certifies = true) :
    FiringPreserves model r (some 2) := by
  apply preserves_after_removing_text model r (some 2) (prefixActions r) 56 tcpState actions untouched
  · intro s f enabled
    rw [shape] at enabled
    exact phaseKnown s f (both s f _ _ enabled).1
  · change FiringPreserves model (cut r) (some 2)
    apply preserves_touched
    intro s f valid _ enabled
    change TypedMachine.eval s f r.guard = true at enabled
    rw [shape] at enabled
    obtain ⟨tcp, link⟩ := both s f _ _ enabled
    have facts := backoff s f valid
    have time := positive_delays s f phase facts
    refine ⟨timing ▸ time, ?_⟩
    intro inv member seen
    have included : inv ∈ affected tcpClauses phase := by
      rw [← catalog]
      exact List.mem_filter.mpr ⟨member, by simp [seen]⟩
    have post : holds (postChecks r phase inv) s f = true := by
      rcases partition phase tcpClauses inv included with tcpMember | linkMember | rfl
      · rw [List.map_inj_left.mp alignment inv tcpMember]
        change (TypedMachine.eval s f (ExprRewrite.run reads inv) && true) = true
        simp [(tcp_post s f tcpState (phaseKnown s f tcp) armed (flight s f tcp) facts).of_mem tcpMember]
      · exact (link_checks s f r phase linkReady link valid).of_mem linkMember
      · exact OctetBounds.all_sound _ (context s f) packetBound
    rw [obligationsFor_split, timing, holds, List.all_append]
    change (holds (delays phase) s f && holds (postChecks r phase inv) s f) = true
    simp [time, post]

private def controlGuard (phase : String) : Expr .boolean :=
  .boolAnd (.equal .text e488 (.literal .text phase)) e3

private theorem control_known (phase : String) (s : Snapshot) (f : Values)
    (input : TypedMachine.eval s f (controlGuard phase) = true) :
    TypedMachine.eval s f e488 = phase :=
  of_decide_eq_true (both s f _ _ input).1

private theorem control (r : Rule) (link : LinkPhase) (phase : String)
    (guard : r.guard = .boolAnd (controlGuard phase) (linkGuard link))
    (nonData : phase ≠ fixedText e807)
    (armed : ArmedPhase phase)
    (actions : r.actions = prefixActions r ++ [.assign .text 56 (.literal .text phase)])
    (untouched : (prefixActions r).all (ignoresAction (.variable .text 56)) = true)
    (catalog : model.invariants.filter (fun inv => !ignoresFiring inv (cut r) (some 2)) =
      affected tcpClauses link)
    (timing : obligationsFor (cut r) (some 2) [] = delays link)
    (alignment : tcpClauses.map (postChecks r link) =
      tcpClauses.map (fun inv => [ExprRewrite.run reads inv]))
    (linkReady : linkCondition r link)
    (packetBound : (postChecks r link e1706).all OctetBounds.certifies = true) :
    FiringPreserves model r (some 2) :=
  certify r link (controlGuard phase) phase guard (control_known phase)
    (fun _ _ _ equal => False.elim (nonData equal)) armed actions untouched catalog timing alignment
    linkReady packetBound

theorem syn_sent_empty : Approved.raw_150_timer_2 :=
  control rule_150 .empty (fixedText e568) rfl (by decide) (by unfold ArmedPhase; decide) rfl
    (by decide +kernel) rfl rfl rfl ⟨⟨by decide +kernel, by decide +kernel, rfl⟩, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩⟩
    (by decide +kernel)

theorem syn_sent_pending : Approved.raw_151_timer_2 :=
  control rule_151 .pending (fixedText e568) rfl (by decide) (by unfold ArmedPhase; decide) rfl
    (by decide +kernel) rfl rfl rfl ⟨by decide +kernel, by decide +kernel, rfl⟩
    (by decide +kernel)

theorem syn_sent_resolved : Approved.raw_152_timer_2 :=
  control rule_152 .resolved (fixedText e568) rfl (by decide) (by unfold ArmedPhase; decide) rfl
    (by decide +kernel) rfl rfl rfl trivial
    (by decide +kernel)

theorem syn_received_empty : Approved.raw_153_timer_2 :=
  control rule_153 .empty (fixedText e740) rfl (by decide) (by unfold ArmedPhase; decide) rfl
    (by decide +kernel) rfl rfl rfl ⟨⟨by decide +kernel, by decide +kernel, rfl⟩, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩⟩
    (by decide +kernel)

theorem syn_received_pending : Approved.raw_154_timer_2 :=
  control rule_154 .pending (fixedText e740) rfl (by decide) (by unfold ArmedPhase; decide) rfl
    (by decide +kernel) rfl rfl rfl ⟨by decide +kernel, by decide +kernel, rfl⟩
    (by decide +kernel)

theorem syn_received_resolved : Approved.raw_155_timer_2 :=
  control rule_155 .resolved (fixedText e740) rfl (by decide) (by unfold ArmedPhase; decide) rfl
    (by decide +kernel) rfl rfl rfl trivial
    (by decide +kernel)

theorem fin_wait_1_empty : Approved.raw_156_timer_2 :=
  control rule_156 .empty (fixedText e940) rfl (by decide) (by unfold ArmedPhase; decide) rfl
    (by decide +kernel) rfl rfl rfl ⟨⟨by decide +kernel, by decide +kernel, rfl⟩, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩⟩
    (by decide +kernel)

theorem fin_wait_1_pending : Approved.raw_157_timer_2 :=
  control rule_157 .pending (fixedText e940) rfl (by decide) (by unfold ArmedPhase; decide) rfl
    (by decide +kernel) rfl rfl rfl ⟨by decide +kernel, by decide +kernel, rfl⟩
    (by decide +kernel)

theorem fin_wait_1_resolved : Approved.raw_158_timer_2 :=
  control rule_158 .resolved (fixedText e940) rfl (by decide) (by unfold ArmedPhase; decide) rfl
    (by decide +kernel) rfl rfl rfl trivial
    (by decide +kernel)

theorem closing_empty : Approved.raw_159_timer_2 :=
  control rule_159 .empty (fixedText e961) rfl (by decide) (by unfold ArmedPhase; decide) rfl
    (by decide +kernel) rfl rfl rfl ⟨⟨by decide +kernel, by decide +kernel, rfl⟩, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩⟩
    (by decide +kernel)

theorem closing_pending : Approved.raw_160_timer_2 :=
  control rule_160 .pending (fixedText e961) rfl (by decide) (by unfold ArmedPhase; decide) rfl
    (by decide +kernel) rfl rfl rfl ⟨by decide +kernel, by decide +kernel, rfl⟩
    (by decide +kernel)

theorem closing_resolved : Approved.raw_161_timer_2 :=
  control rule_161 .resolved (fixedText e961) rfl (by decide) (by unfold ArmedPhase; decide) rfl
    (by decide +kernel) rfl rfl rfl trivial
    (by decide +kernel)

theorem last_ack_empty : Approved.raw_162_timer_2 :=
  control rule_162 .empty (fixedText e947) rfl (by decide) (by unfold ArmedPhase; decide) rfl
    (by decide +kernel) rfl rfl rfl ⟨⟨by decide +kernel, by decide +kernel, rfl⟩, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩⟩
    (by decide +kernel)

theorem last_ack_pending : Approved.raw_163_timer_2 :=
  control rule_163 .pending (fixedText e947) rfl (by decide) (by unfold ArmedPhase; decide) rfl
    (by decide +kernel) rfl rfl rfl ⟨by decide +kernel, by decide +kernel, rfl⟩
    (by decide +kernel)

theorem last_ack_resolved : Approved.raw_164_timer_2 :=
  control rule_164 .resolved (fixedText e947) rfl (by decide) (by unfold ArmedPhase; decide) rfl
    (by decide +kernel) rfl rfl rfl trivial
    (by decide +kernel)

private theorem data (r : Rule) (link : LinkPhase)
    (guard : r.guard = .boolAnd e1328 (linkGuard link))
    (actions : r.actions = prefixActions r ++ [.assign .text 56 e807])
    (untouched : (prefixActions r).all (ignoresAction (.variable .text 56)) = true)
    (catalog : model.invariants.filter (fun inv => !ignoresFiring inv (cut r) (some 2)) =
      affected tcpClauses link)
    (timing : obligationsFor (cut r) (some 2) [] = delays link)
    (alignment : tcpClauses.map (postChecks r link) =
      tcpClauses.map (fun inv => [ExprRewrite.run reads inv]))
    (linkReady : linkCondition r link)
    (packetBound : (postChecks r link e1706).all OctetBounds.certifies = true) :
    FiringPreserves model r (some 2) :=
  certify r link e1328 (fixedText e807) guard
    (fun s f enabled => of_decide_eq_true (both s f e923 e1243 enabled).1)
    (fun s f enabled _ => (both s f e923 e1243 enabled).2)
    (by unfold ArmedPhase; decide) actions untouched catalog timing alignment linkReady packetBound

theorem data_empty : Approved.raw_258_timer_2 :=
  data rule_258 .empty rfl rfl (by decide +kernel) rfl rfl rfl ⟨⟨by decide +kernel, by decide +kernel, rfl⟩, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩⟩
    (by decide +kernel)

theorem data_pending : Approved.raw_259_timer_2 :=
  data rule_259 .pending rfl rfl (by decide +kernel) rfl rfl rfl ⟨by decide +kernel, by decide +kernel, rfl⟩
    (by decide +kernel)

theorem data_resolved : Approved.raw_260_timer_2 :=
  data rule_260 .resolved rfl rfl (by decide +kernel) rfl rfl rfl trivial
    (by decide +kernel)

def firings : List (Rule × Option Nat) :=
  [(rule_150, some 2), (rule_151, some 2), (rule_152, some 2),
   (rule_153, some 2), (rule_154, some 2), (rule_155, some 2),
   (rule_156, some 2), (rule_157, some 2), (rule_158, some 2),
   (rule_159, some 2), (rule_160, some 2), (rule_161, some 2),
   (rule_162, some 2), (rule_163, some 2), (rule_164, some 2),
   (rule_258, some 2), (rule_259, some 2), (rule_260, some 2)]

theorem checked : Each (fun p => FiringPreserves model p.1 p.2) firings :=
  ⟨syn_sent_empty, syn_sent_pending, syn_sent_resolved,
   syn_received_empty, syn_received_pending, syn_received_resolved,
   fin_wait_1_empty, fin_wait_1_pending, fin_wait_1_resolved,
   closing_empty, closing_pending, closing_resolved,
   last_ack_empty, last_ack_pending, last_ack_resolved,
   data_empty, data_pending, data_resolved,
   trivial⟩

private theorem timerMember (index : Nat) (r : Rule)
    (selected : model.rules[index]? = some r) (trigger : r.event = model.timerEvents 2) :
    (r, some 2) ∈ rawChecks model declaredTimers :=
  raw_timer_member model declaredTimers r 2 (List.mem_iff_getElem?.mpr ⟨index, selected⟩)
    (by decide) trigger

theorem members : Each (fun p => p ∈ rawChecks model declaredTimers) firings :=
  ⟨timerMember 150 rule_150 rfl rfl, timerMember 151 rule_151 rfl rfl,
   timerMember 152 rule_152 rfl rfl, timerMember 153 rule_153 rfl rfl,
   timerMember 154 rule_154 rfl rfl, timerMember 155 rule_155 rfl rfl,
   timerMember 156 rule_156 rfl rfl, timerMember 157 rule_157 rfl rfl,
   timerMember 158 rule_158 rfl rfl, timerMember 159 rule_159 rfl rfl,
   timerMember 160 rule_160 rfl rfl, timerMember 161 rule_161 rfl rfl,
   timerMember 162 rule_162 rfl rfl, timerMember 163 rule_163 rfl rfl,
   timerMember 164 rule_164 rfl rfl, timerMember 258 rule_258 rfl rfl,
   timerMember 259 rule_259 rfl rfl, timerMember 260 rule_260 rfl rfl,
   trivial⟩

end TCPIPRetransmit
