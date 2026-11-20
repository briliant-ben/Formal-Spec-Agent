import TCPIPSendWire
import GuardedSuffix
import TCPIPQueueRelease

namespace TCPIPControlReplies
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts
open EffectConditions EffectFootprint GuardedSuffix TimedObligations TCPIPSendWire
set_option maxRecDepth 16384

private abbrev fixedText (e : Expr .text) := TypedMachine.eval initial zeroValues e
private def prefixActions (r : Rule) := r.actions.dropLast
private def cut (r : Rule) : Rule := {r with actions := prefixActions r}

private def body (phase : String) (select : Expr .boolean) : Expr .boolean :=
  .boolAnd (.boolAnd (.equal .text e488 (.literal .text phase)) select) e721

private theorem both (s : Snapshot) (f : Values) (x y : Expr .boolean)
    (enabled : TypedMachine.eval s f (.boolAnd x y) = true) :
    TypedMachine.eval s f x = true ∧ TypedMachine.eval s f y = true := by
  change (TypedMachine.eval s f x && TypedMachine.eval s f y) = true at enabled
  simpa only [Bool.and_eq_true] using enabled

private theorem known (s : Snapshot) (f : Values) (phase : String) (select : Expr .boolean)
    (enabled : TypedMachine.eval s f (body phase select) = true) :
    TypedMachine.eval s f e488 = phase :=
  of_decide_eq_true (both s f _ _ (both s f _ _ enabled).1).1

private inductive ReplyEffect where
  | keepTimers | restartTimeWait | releaseQueue

private def delays (effect : ReplyEffect) (phase : LinkPhase) : List (Expr .boolean) :=
  (match phase with | .empty => [.intGe e10 e44] | _ => []) ++
    (match effect with | .restartTimeWait => [.intGe e985 e44] | _ => [])

private def tcpClauses : ReplyEffect → List (Expr .boolean)
  | .restartTimeWait => [e1637, e1640, e1645, e1648, e1650, e1653, e1656, e1659, e1662, e1665, e1669]
  | _ => []

private def reads : ExprRewrite.Rewrite :=
  { varRead := Expr.variable
    field := fun kind slot => .literal kind (getValue kind zeroValues slot)
    stateIs := fun id => .literal .boolean (decide (0 = id))
    timerActive := fun owner => if owner = 3 then .literal .boolean true else .timerActive owner }

private theorem tcp_post (s : Snapshot) (f : Values)
    (state : TypedMachine.eval s f e488 = fixedText e966) :
    Each (fun inv => TypedMachine.eval s f (ExprRewrite.run reads inv) = true) (tcpClauses .restartTimeWait) := by
  have different (phase : String) (distinct : fixedText e966 ≠ phase) :
      decide (TypedMachine.eval s f e488 = phase) = false := by
    rw [state]
    exact decide_eq_false distinct
  have closed : TypedMachine.eval s f e489 = false := different (fixedText e14) (by decide)
  have listen : TypedMachine.eval s f e580 = false := different (fixedText e579) (by decide)
  have sent : TypedMachine.eval s f e743 = false := different (fixedText e568) (by decide)
  have received : TypedMachine.eval s f e810 = false := different (fixedText e740) (by decide)
  have established : TypedMachine.eval s f e923 = false := different (fixedText e807) (by decide)
  have fw1 : TypedMachine.eval s f e955 = false := different (fixedText e940) (by decide)
  have closeWait : TypedMachine.eval s f e959 = false := different (fixedText e958) (by decide)
  have fw2 : TypedMachine.eval s f e944 = false := different (fixedText e943) (by decide)
  have closing : TypedMachine.eval s f e962 = false := different (fixedText e961) (by decide)
  have lastAck : TypedMachine.eval s f e964 = false := different (fixedText e947) (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · change (!TypedMachine.eval s f e489 || false) = true; simp [closed]
  · change (!TypedMachine.eval s f e580 || false) = true; simp [listen]
  · change (!TypedMachine.eval s f e743 || false) = true; simp [sent]
  · change (!TypedMachine.eval s f e810 || false) = true; simp [received]
  · change (!TypedMachine.eval s f e923 || false) = true; simp [established]
  · change (!TypedMachine.eval s f e955 || false) = true; simp [fw1]
  · change (!TypedMachine.eval s f e959 || false) = true; simp [closeWait]
  · change (!TypedMachine.eval s f e944 || false) = true; simp [fw2]
  · change (!TypedMachine.eval s f e962 || false) = true; simp [closing]
  · change (!TypedMachine.eval s f e964 || false) = true; simp [lastAck]
  · change (!TypedMachine.eval s f e967 || true) = true; simp

private theorem positive_delays (s : Snapshot) (f : Values) (effect : ReplyEffect) (phase : LinkPhase)
    (valid : invariantsHold model s = true) : holds (delays effect phase) s f = true := by
  have before : 1 ≤ TypedMachine.eval s f e984 :=
    of_decide_eq_true (List.all_eq_true.mp valid e1682 (by rw [model_invariants]; simp))
  have doubled (n : Int) (lower : 1 ≤ n) : 1 ≤ n * 2 := by omega
  have positive : 1 ≤ TypedMachine.eval s f e985 := doubled _ before
  cases effect <;> cases phase
  all_goals first | rfl | (change (decide (1 ≤ TypedMachine.eval s f e985) && true) = true; simp [positive])

private def postChecks (r : Rule) (phase : LinkPhase) (effect : ReplyEffect) (inv : Expr .boolean) :
    List (Expr .boolean) :=
  (obligationsFor (cut r) none [inv]).drop (delays effect phase).length

private def tracked (effect : ReplyEffect) (phase : LinkPhase) : List (Expr .boolean) :=
  match effect with
  | .releaseQueue => [e1612, e1614, e1615, e1706, e1721]
  | _ => affected (tcpClauses effect) phase

private theorem certify (r : Rule) (phase : LinkPhase) (state : String) (select : Expr .boolean) (effect : ReplyEffect)
    (guard : r.guard = .boolAnd (body state select) (linkGuard phase))
    (timeWait : effect = .restartTimeWait → state = fixedText e966)
    (actions : r.actions = prefixActions r ++ [.assign .text 56 (.literal .text state)])
    (untouched : (prefixActions r).all (ignoresAction (.variable .text 56)) = true)
    (catalog : model.invariants.filter (fun inv => !ignoresFiring inv (cut r) none) =
      tracked effect phase)
    (timing : obligationsFor (cut r) none [] = delays effect phase)
    (alignment : (tcpClauses effect).map (postChecks r phase effect) =
      (tcpClauses effect).map (fun inv => [ExprRewrite.run reads inv]))
    (linkReady : linkCondition (postChecks r phase effect) phase)
    (release : effect = .releaseQueue → TCPIPQueueRelease.queueClauses.map (postChecks r phase effect) =
      TCPIPQueueRelease.queueClauses.map (fun inv => [ExprRewrite.run TCPIPQueueRelease.releaseReads inv]))
    (packetBound : (postChecks r phase effect e1706).all OctetBounds.certifies = true) :
    FiringPreserves model r none := by
  apply preserves_after_removing_text model r none (prefixActions r) 56 state actions untouched
  · intro s f enabled
    rw [guard] at enabled
    exact known s f state select (both s f _ _ enabled).1
  · change FiringPreserves model (cut r) none
    apply preserves_touched
    intro s f valid _ enabled
    change TypedMachine.eval s f r.guard = true at enabled
    rw [guard] at enabled
    obtain ⟨tcp, link⟩ := both s f _ _ enabled
    have time := positive_delays s f effect phase valid
    refine ⟨timing ▸ time, ?_⟩
    intro inv member seen
    have included : inv ∈ tracked effect phase := by
      rw [← catalog]
      exact List.mem_filter.mpr ⟨member, by simp [seen]⟩
    have post : holds (postChecks r phase effect inv) s f = true := by
      cases effect
      · rcases partition phase (tcpClauses .keepTimers) inv included with tcpMember | linkMember | rfl
        · exact False.elim (List.not_mem_nil tcpMember)
        · exact (link_checks s f _ phase linkReady link valid).of_mem linkMember
        · exact OctetBounds.all_sound _ (context s f) packetBound
      · rcases partition phase (tcpClauses .restartTimeWait) inv included with tcpMember | linkMember | rfl
        · rw [List.map_inj_left.mp alignment inv tcpMember]
          change (TypedMachine.eval s f (ExprRewrite.run reads inv) && true) = true
          have atWait := (known s f state select tcp).trans (timeWait rfl)
          simp [(tcp_post s f atWait).of_mem tcpMember]
        · exact (link_checks s f _ phase linkReady link valid).of_mem linkMember
        · exact OctetBounds.all_sound _ (context s f) packetBound
      · have relevant : inv ∈ TCPIPQueueRelease.queueClauses ∨ inv = e1706 := by
          simpa only [tracked, TCPIPQueueRelease.queueClauses, List.mem_cons,
            List.not_mem_nil, or_false, or_assoc, or_comm, or_left_comm] using included
        rcases relevant with queue | rfl
        · rw [List.map_inj_left.mp (release rfl) inv queue]
          change (TypedMachine.eval s f (ExprRewrite.run TCPIPQueueRelease.releaseReads inv) && true) = true
          simp [(TCPIPQueueRelease.release_queue_safe s f valid).of_mem queue]
        · exact OctetBounds.all_sound _ (context s f) packetBound
    rw [obligationsFor_split, timing, holds, List.all_append]
    change (holds (delays effect phase) s f && holds (postChecks r phase effect inv) s f) = true
    simp [time, post]

theorem syn_sent_bad_ack_empty : Approved.raw_95_external :=
  certify rule_95 .empty (fixedText e568) e877 .keepTimers rfl
    (by intro impossible; cases impossible) rfl (by decide +kernel) rfl rfl rfl
    ⟨⟨by decide +kernel, by decide +kernel, rfl⟩, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩⟩ (by intro impossible; cases impossible) (by decide +kernel)

theorem syn_sent_bad_ack_pending : Approved.raw_96_external :=
  certify rule_96 .pending (fixedText e568) e877 .keepTimers rfl
    (by intro impossible; cases impossible) rfl (by decide +kernel) rfl rfl rfl
    ⟨by decide +kernel, by decide +kernel, rfl⟩ (by intro impossible; cases impossible) (by decide +kernel)

theorem syn_sent_bad_ack_resolved : Approved.raw_97_external :=
  certify rule_97 .resolved (fixedText e568) e877 .keepTimers rfl
    (by intro impossible; cases impossible) rfl (by decide +kernel) rfl rfl rfl
    trivial (by intro impossible; cases impossible) (by decide +kernel)

theorem syn_sent_bad_synack_empty : Approved.raw_98_external :=
  certify rule_98 .empty (fixedText e568) e907 .keepTimers rfl
    (by intro impossible; cases impossible) rfl (by decide +kernel) rfl rfl rfl
    ⟨⟨by decide +kernel, by decide +kernel, rfl⟩, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩⟩ (by intro impossible; cases impossible) (by decide +kernel)

theorem syn_sent_bad_synack_pending : Approved.raw_99_external :=
  certify rule_99 .pending (fixedText e568) e907 .keepTimers rfl
    (by intro impossible; cases impossible) rfl (by decide +kernel) rfl rfl rfl
    ⟨by decide +kernel, by decide +kernel, rfl⟩ (by intro impossible; cases impossible) (by decide +kernel)

theorem syn_sent_bad_synack_resolved : Approved.raw_100_external :=
  certify rule_100 .resolved (fixedText e568) e907 .keepTimers rfl
    (by intro impossible; cases impossible) rfl (by decide +kernel) rfl rfl rfl
    trivial (by intro impossible; cases impossible) (by decide +kernel)

theorem syn_received_bad_ack_empty : Approved.raw_102_external :=
  certify rule_102 .empty (fixedText e740) e917 .keepTimers rfl
    (by intro impossible; cases impossible) rfl (by decide +kernel) rfl rfl rfl
    ⟨⟨by decide +kernel, by decide +kernel, rfl⟩, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩⟩ (by intro impossible; cases impossible) (by decide +kernel)

theorem syn_received_bad_ack_pending : Approved.raw_103_external :=
  certify rule_103 .pending (fixedText e740) e917 .keepTimers rfl
    (by intro impossible; cases impossible) rfl (by decide +kernel) rfl rfl rfl
    ⟨by decide +kernel, by decide +kernel, rfl⟩ (by intro impossible; cases impossible) (by decide +kernel)

theorem syn_received_bad_ack_resolved : Approved.raw_104_external :=
  certify rule_104 .resolved (fixedText e740) e917 .keepTimers rfl
    (by intro impossible; cases impossible) rfl (by decide +kernel) rfl rfl rfl
    trivial (by intro impossible; cases impossible) (by decide +kernel)

theorem close_wait_fin_empty : Approved.raw_138_external :=
  certify rule_138 .empty (fixedText e943) e1022 .keepTimers rfl
    (by intro impossible; cases impossible) rfl (by decide +kernel) rfl rfl rfl
    ⟨⟨by decide +kernel, by decide +kernel, rfl⟩, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩⟩ (by intro impossible; cases impossible) (by decide +kernel)

theorem close_wait_fin_pending : Approved.raw_139_external :=
  certify rule_139 .pending (fixedText e943) e1022 .keepTimers rfl
    (by intro impossible; cases impossible) rfl (by decide +kernel) rfl rfl rfl
    ⟨by decide +kernel, by decide +kernel, rfl⟩ (by intro impossible; cases impossible) (by decide +kernel)

theorem close_wait_fin_resolved : Approved.raw_140_external :=
  certify rule_140 .resolved (fixedText e943) e1022 .keepTimers rfl
    (by intro impossible; cases impossible) rfl (by decide +kernel) rfl rfl rfl
    trivial (by intro impossible; cases impossible) (by decide +kernel)

theorem closing_fin_empty : Approved.raw_141_external :=
  certify rule_141 .empty (fixedText e961) e1022 .keepTimers rfl
    (by intro impossible; cases impossible) rfl (by decide +kernel) rfl rfl rfl
    ⟨⟨by decide +kernel, by decide +kernel, rfl⟩, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩⟩ (by intro impossible; cases impossible) (by decide +kernel)

theorem closing_fin_pending : Approved.raw_142_external :=
  certify rule_142 .pending (fixedText e961) e1022 .keepTimers rfl
    (by intro impossible; cases impossible) rfl (by decide +kernel) rfl rfl rfl
    ⟨by decide +kernel, by decide +kernel, rfl⟩ (by intro impossible; cases impossible) (by decide +kernel)

theorem closing_fin_resolved : Approved.raw_143_external :=
  certify rule_143 .resolved (fixedText e961) e1022 .keepTimers rfl
    (by intro impossible; cases impossible) rfl (by decide +kernel) rfl rfl rfl
    trivial (by intro impossible; cases impossible) (by decide +kernel)

theorem last_ack_fin_empty : Approved.raw_144_external :=
  certify rule_144 .empty (fixedText e947) e1022 .keepTimers rfl
    (by intro impossible; cases impossible) rfl (by decide +kernel) rfl rfl rfl
    ⟨⟨by decide +kernel, by decide +kernel, rfl⟩, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩⟩ (by intro impossible; cases impossible) (by decide +kernel)

theorem last_ack_fin_pending : Approved.raw_145_external :=
  certify rule_145 .pending (fixedText e947) e1022 .keepTimers rfl
    (by intro impossible; cases impossible) rfl (by decide +kernel) rfl rfl rfl
    ⟨by decide +kernel, by decide +kernel, rfl⟩ (by intro impossible; cases impossible) (by decide +kernel)

theorem last_ack_fin_resolved : Approved.raw_146_external :=
  certify rule_146 .resolved (fixedText e947) e1022 .keepTimers rfl
    (by intro impossible; cases impossible) rfl (by decide +kernel) rfl rfl rfl
    trivial (by intro impossible; cases impossible) (by decide +kernel)

theorem time_wait_fin_empty : Approved.raw_147_external :=
  certify rule_147 .empty (fixedText e966) e1022 .restartTimeWait rfl
    (fun _ => rfl) rfl (by decide +kernel) rfl rfl rfl
    ⟨⟨by decide +kernel, by decide +kernel, rfl⟩, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩⟩ (by intro impossible; cases impossible) (by decide +kernel)

theorem time_wait_fin_pending : Approved.raw_148_external :=
  certify rule_148 .pending (fixedText e966) e1022 .restartTimeWait rfl
    (fun _ => rfl) rfl (by decide +kernel) rfl rfl rfl
    ⟨by decide +kernel, by decide +kernel, rfl⟩ (by intro impossible; cases impossible) (by decide +kernel)

theorem time_wait_fin_resolved : Approved.raw_149_external :=
  certify rule_149 .resolved (fixedText e966) e1022 .restartTimeWait rfl
    (fun _ => rfl) rfl (by decide +kernel) rfl rfl rfl
    trivial (by intro impossible; cases impossible) (by decide +kernel)

theorem closed_syn_empty : Approved.raw_235_external :=
  certify rule_235 .empty (fixedText e14) e672 .keepTimers rfl
    (by intro impossible; cases impossible) rfl (by decide +kernel) rfl rfl rfl
    ⟨⟨by decide +kernel, by decide +kernel, rfl⟩, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩⟩ (by intro impossible; cases impossible) (by decide +kernel)

theorem closed_syn_pending : Approved.raw_236_external :=
  certify rule_236 .pending (fixedText e14) e672 .keepTimers rfl
    (by intro impossible; cases impossible) rfl (by decide +kernel) rfl rfl rfl
    ⟨by decide +kernel, by decide +kernel, rfl⟩ (by intro impossible; cases impossible) (by decide +kernel)

theorem closed_syn_resolved : Approved.raw_237_external :=
  certify rule_237 .resolved (fixedText e14) e672 .releaseQueue rfl
    (by intro impossible; cases impossible) rfl (by decide +kernel) rfl rfl rfl
    trivial (fun _ => rfl) (by decide +kernel)

theorem closed_ack_empty : Approved.raw_217_external :=
  certify rule_217 .empty (fixedText e14) e1144 .keepTimers rfl
    (by intro impossible; cases impossible) rfl (by decide +kernel) rfl rfl rfl
    ⟨⟨by decide +kernel, by decide +kernel, rfl⟩, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩⟩ (by intro impossible; cases impossible) (by decide +kernel)

theorem closed_ack_pending : Approved.raw_218_external :=
  certify rule_218 .pending (fixedText e14) e1144 .keepTimers rfl
    (by intro impossible; cases impossible) rfl (by decide +kernel) rfl rfl rfl
    ⟨by decide +kernel, by decide +kernel, rfl⟩ (by intro impossible; cases impossible) (by decide +kernel)

theorem closed_ack_resolved : Approved.raw_219_external :=
  certify rule_219 .resolved (fixedText e14) e1144 .releaseQueue rfl
    (by intro impossible; cases impossible) rfl (by decide +kernel) rfl rfl rfl
    trivial (fun _ => rfl) (by decide +kernel)

theorem listen_ack_empty : Approved.raw_220_external :=
  certify rule_220 .empty (fixedText e579) e1144 .keepTimers rfl
    (by intro impossible; cases impossible) rfl (by decide +kernel) rfl rfl rfl
    ⟨⟨by decide +kernel, by decide +kernel, rfl⟩, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩⟩ (by intro impossible; cases impossible) (by decide +kernel)

theorem listen_ack_pending : Approved.raw_221_external :=
  certify rule_221 .pending (fixedText e579) e1144 .keepTimers rfl
    (by intro impossible; cases impossible) rfl (by decide +kernel) rfl rfl rfl
    ⟨by decide +kernel, by decide +kernel, rfl⟩ (by intro impossible; cases impossible) (by decide +kernel)

theorem listen_ack_resolved : Approved.raw_222_external :=
  certify rule_222 .resolved (fixedText e579) e1144 .keepTimers rfl
    (by intro impossible; cases impossible) rfl (by decide +kernel) rfl rfl rfl
    trivial (by intro impossible; cases impossible) (by decide +kernel)

theorem closed_synack_empty : Approved.raw_223_external :=
  certify rule_223 .empty (fixedText e14) e1155 .keepTimers rfl
    (by intro impossible; cases impossible) rfl (by decide +kernel) rfl rfl rfl
    ⟨⟨by decide +kernel, by decide +kernel, rfl⟩, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩⟩ (by intro impossible; cases impossible) (by decide +kernel)

theorem closed_synack_pending : Approved.raw_224_external :=
  certify rule_224 .pending (fixedText e14) e1155 .keepTimers rfl
    (by intro impossible; cases impossible) rfl (by decide +kernel) rfl rfl rfl
    ⟨by decide +kernel, by decide +kernel, rfl⟩ (by intro impossible; cases impossible) (by decide +kernel)

theorem closed_synack_resolved : Approved.raw_225_external :=
  certify rule_225 .resolved (fixedText e14) e1155 .releaseQueue rfl
    (by intro impossible; cases impossible) rfl (by decide +kernel) rfl rfl rfl
    trivial (fun _ => rfl) (by decide +kernel)

theorem listen_synack_empty : Approved.raw_226_external :=
  certify rule_226 .empty (fixedText e579) e1155 .keepTimers rfl
    (by intro impossible; cases impossible) rfl (by decide +kernel) rfl rfl rfl
    ⟨⟨by decide +kernel, by decide +kernel, rfl⟩, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩⟩ (by intro impossible; cases impossible) (by decide +kernel)

theorem listen_synack_pending : Approved.raw_227_external :=
  certify rule_227 .pending (fixedText e579) e1155 .keepTimers rfl
    (by intro impossible; cases impossible) rfl (by decide +kernel) rfl rfl rfl
    ⟨by decide +kernel, by decide +kernel, rfl⟩ (by intro impossible; cases impossible) (by decide +kernel)

theorem listen_synack_resolved : Approved.raw_228_external :=
  certify rule_228 .resolved (fixedText e579) e1155 .keepTimers rfl
    (by intro impossible; cases impossible) rfl (by decide +kernel) rfl rfl rfl
    trivial (by intro impossible; cases impossible) (by decide +kernel)

theorem closed_fin_empty : Approved.raw_229_external :=
  certify rule_229 .empty (fixedText e14) e1166 .keepTimers rfl
    (by intro impossible; cases impossible) rfl (by decide +kernel) rfl rfl rfl
    ⟨⟨by decide +kernel, by decide +kernel, rfl⟩, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩⟩ (by intro impossible; cases impossible) (by decide +kernel)

theorem closed_fin_pending : Approved.raw_230_external :=
  certify rule_230 .pending (fixedText e14) e1166 .keepTimers rfl
    (by intro impossible; cases impossible) rfl (by decide +kernel) rfl rfl rfl
    ⟨by decide +kernel, by decide +kernel, rfl⟩ (by intro impossible; cases impossible) (by decide +kernel)

theorem closed_fin_resolved : Approved.raw_231_external :=
  certify rule_231 .resolved (fixedText e14) e1166 .releaseQueue rfl
    (by intro impossible; cases impossible) rfl (by decide +kernel) rfl rfl rfl
    trivial (fun _ => rfl) (by decide +kernel)

theorem listen_fin_empty : Approved.raw_232_external :=
  certify rule_232 .empty (fixedText e579) e1166 .keepTimers rfl
    (by intro impossible; cases impossible) rfl (by decide +kernel) rfl rfl rfl
    ⟨⟨by decide +kernel, by decide +kernel, rfl⟩, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩⟩ (by intro impossible; cases impossible) (by decide +kernel)

theorem listen_fin_pending : Approved.raw_233_external :=
  certify rule_233 .pending (fixedText e579) e1166 .keepTimers rfl
    (by intro impossible; cases impossible) rfl (by decide +kernel) rfl rfl rfl
    ⟨by decide +kernel, by decide +kernel, rfl⟩ (by intro impossible; cases impossible) (by decide +kernel)

theorem listen_fin_resolved : Approved.raw_234_external :=
  certify rule_234 .resolved (fixedText e579) e1166 .keepTimers rfl
    (by intro impossible; cases impossible) rfl (by decide +kernel) rfl rfl rfl
    trivial (by intro impossible; cases impossible) (by decide +kernel)

def firings : List (Rule × Option Nat) :=
  [(rule_95, none), (rule_96, none), (rule_97, none), (rule_98, none),
   (rule_99, none), (rule_100, none), (rule_102, none), (rule_103, none),
   (rule_104, none), (rule_138, none), (rule_139, none), (rule_140, none),
   (rule_141, none), (rule_142, none), (rule_143, none), (rule_144, none),
   (rule_145, none), (rule_146, none), (rule_147, none), (rule_148, none),
   (rule_149, none), (rule_217, none), (rule_218, none), (rule_219, none),
   (rule_220, none), (rule_221, none), (rule_222, none), (rule_223, none),
   (rule_224, none), (rule_225, none), (rule_226, none), (rule_227, none),
   (rule_228, none), (rule_229, none), (rule_230, none), (rule_231, none),
   (rule_232, none), (rule_233, none), (rule_234, none), (rule_235, none),
   (rule_236, none), (rule_237, none)]

theorem checked : Each (fun p => FiringPreserves model p.1 p.2) firings :=
  ⟨syn_sent_bad_ack_empty, syn_sent_bad_ack_pending, syn_sent_bad_ack_resolved,
   syn_sent_bad_synack_empty, syn_sent_bad_synack_pending, syn_sent_bad_synack_resolved,
   syn_received_bad_ack_empty, syn_received_bad_ack_pending, syn_received_bad_ack_resolved,
   close_wait_fin_empty, close_wait_fin_pending, close_wait_fin_resolved,
   closing_fin_empty, closing_fin_pending, closing_fin_resolved,
   last_ack_fin_empty, last_ack_fin_pending, last_ack_fin_resolved,
   time_wait_fin_empty, time_wait_fin_pending, time_wait_fin_resolved,
   closed_ack_empty, closed_ack_pending, closed_ack_resolved,
   listen_ack_empty, listen_ack_pending, listen_ack_resolved,
   closed_synack_empty, closed_synack_pending, closed_synack_resolved,
   listen_synack_empty, listen_synack_pending, listen_synack_resolved,
   closed_fin_empty, closed_fin_pending, closed_fin_resolved,
   listen_fin_empty, listen_fin_pending, listen_fin_resolved,
   closed_syn_empty, closed_syn_pending, closed_syn_resolved,
   trivial⟩

private theorem replyMember (index : Nat) (r : Rule)
    (selected : model.rules[index]? = some r) (external : r.event ∈ model.externalEvents) :
    (r, none) ∈ rawChecks model declaredTimers :=
  raw_external_member model declaredTimers r (List.mem_iff_getElem?.mpr ⟨index, selected⟩) external

theorem members : Each (fun p => p ∈ rawChecks model declaredTimers) firings :=
  ⟨replyMember 95 rule_95 rfl (by decide), replyMember 96 rule_96 rfl (by decide),
   replyMember 97 rule_97 rfl (by decide), replyMember 98 rule_98 rfl (by decide),
   replyMember 99 rule_99 rfl (by decide), replyMember 100 rule_100 rfl (by decide),
   replyMember 102 rule_102 rfl (by decide), replyMember 103 rule_103 rfl (by decide),
   replyMember 104 rule_104 rfl (by decide), replyMember 138 rule_138 rfl (by decide),
   replyMember 139 rule_139 rfl (by decide), replyMember 140 rule_140 rfl (by decide),
   replyMember 141 rule_141 rfl (by decide), replyMember 142 rule_142 rfl (by decide),
   replyMember 143 rule_143 rfl (by decide), replyMember 144 rule_144 rfl (by decide),
   replyMember 145 rule_145 rfl (by decide), replyMember 146 rule_146 rfl (by decide),
   replyMember 147 rule_147 rfl (by decide), replyMember 148 rule_148 rfl (by decide),
   replyMember 149 rule_149 rfl (by decide), replyMember 217 rule_217 rfl (by decide),
   replyMember 218 rule_218 rfl (by decide), replyMember 219 rule_219 rfl (by decide),
   replyMember 220 rule_220 rfl (by decide), replyMember 221 rule_221 rfl (by decide),
   replyMember 222 rule_222 rfl (by decide), replyMember 223 rule_223 rfl (by decide),
   replyMember 224 rule_224 rfl (by decide), replyMember 225 rule_225 rfl (by decide),
   replyMember 226 rule_226 rfl (by decide), replyMember 227 rule_227 rfl (by decide),
   replyMember 228 rule_228 rfl (by decide), replyMember 229 rule_229 rfl (by decide),
   replyMember 230 rule_230 rfl (by decide), replyMember 231 rule_231 rfl (by decide),
   replyMember 232 rule_232 rfl (by decide), replyMember 233 rule_233 rfl (by decide),
   replyMember 234 rule_234 rfl (by decide), replyMember 235 rule_235 rfl (by decide),
   replyMember 236 rule_236 rfl (by decide), replyMember 237 rule_237 rfl (by decide),
   trivial⟩

end TCPIPControlReplies
