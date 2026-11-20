import TCPIPSendWire
import GuardedSuffix

namespace TCPIPDuplicateFin
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts
open EffectConditions EffectFootprint GuardedSuffix TimedObligations TCPIPSendWire
set_option maxRecDepth 16384

private abbrev fixedText (e : Expr .text) := TypedMachine.eval initial zeroValues e
private def prefixActions (r : Rule) := r.actions.dropLast
private def cut (r : Rule) : Rule := {r with actions := prefixActions r}

private def body (phase : String) : Expr .boolean :=
  .boolAnd (.boolAnd (.equal .text e488 (.literal .text phase)) e1022) e721

private theorem both (s : Snapshot) (f : Values) (x y : Expr .boolean)
    (enabled : TypedMachine.eval s f (.boolAnd x y) = true) :
    TypedMachine.eval s f x = true ∧ TypedMachine.eval s f y = true := by
  change (TypedMachine.eval s f x && TypedMachine.eval s f y) = true at enabled
  simpa only [Bool.and_eq_true] using enabled

private theorem known (s : Snapshot) (f : Values) (phase : String)
    (enabled : TypedMachine.eval s f (body phase) = true) :
    TypedMachine.eval s f e488 = phase :=
  of_decide_eq_true (both s f _ _ (both s f _ _ enabled).1).1

private def delays (restart : Bool) (phase : LinkPhase) : List (Expr .boolean) :=
  (match phase with | .empty => [.intGe e10 e44] | _ => []) ++
    (if restart then [.intGe e985 e44] else [])

private def tcpClauses (restart : Bool) : List (Expr .boolean) :=
  if restart then [e1637, e1640, e1645, e1648, e1650, e1653, e1656, e1659, e1662, e1665, e1669] else []

private def reads : ExprRewrite.Rewrite :=
  { varRead := Expr.variable
    field := fun kind slot => .literal kind (getValue kind zeroValues slot)
    stateIs := fun id => .literal .boolean (decide (0 = id))
    timerActive := fun owner => if owner = 3 then .literal .boolean true else .timerActive owner }

private theorem tcp_post (s : Snapshot) (f : Values)
    (state : TypedMachine.eval s f e488 = fixedText e966) :
    Each (fun inv => TypedMachine.eval s f (ExprRewrite.run reads inv) = true) (tcpClauses true) := by
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

private theorem positive_delays (s : Snapshot) (f : Values) (restart : Bool) (phase : LinkPhase)
    (valid : invariantsHold model s = true) : holds (delays restart phase) s f = true := by
  have before : 1 ≤ TypedMachine.eval s f e984 :=
    of_decide_eq_true (List.all_eq_true.mp valid e1682 (by rw [model_invariants]; simp))
  have doubled (n : Int) (lower : 1 ≤ n) : 1 ≤ n * 2 := by omega
  have positive : 1 ≤ TypedMachine.eval s f e985 := doubled _ before
  cases restart <;> cases phase
  all_goals first | rfl | (change (decide (1 ≤ TypedMachine.eval s f e985) && true) = true; simp [positive])

private def postChecks (r : Rule) (phase : LinkPhase) (restart : Bool) (inv : Expr .boolean) :
    List (Expr .boolean) :=
  (obligationsFor (cut r) none [inv]).drop (delays restart phase).length

private theorem certify (r : Rule) (phase : LinkPhase) (state : String) (restart : Bool)
    (guard : r.guard = .boolAnd (body state) (linkGuard phase))
    (timeWait : restart = true → state = fixedText e966)
    (actions : r.actions = prefixActions r ++ [.assign .text 56 (.literal .text state)])
    (untouched : (prefixActions r).all (ignoresAction (.variable .text 56)) = true)
    (catalog : model.invariants.filter (fun inv => !ignoresFiring inv (cut r) none) =
      affected (tcpClauses restart) phase)
    (timing : obligationsFor (cut r) none [] = delays restart phase)
    (alignment : (tcpClauses restart).map (postChecks r phase restart) =
      (tcpClauses restart).map (fun inv => [ExprRewrite.run reads inv]))
    (linkReady : linkCondition (postChecks r phase restart) phase)
    (packetBound : (postChecks r phase restart e1706).all OctetBounds.certifies = true) :
    FiringPreserves model r none := by
  apply preserves_after_removing_text model r none (prefixActions r) 56 state actions untouched
  · intro s f enabled
    rw [guard] at enabled
    exact known s f state (both s f _ _ enabled).1
  · change FiringPreserves model (cut r) none
    apply preserves_touched
    intro s f valid _ enabled
    change TypedMachine.eval s f r.guard = true at enabled
    rw [guard] at enabled
    obtain ⟨tcp, link⟩ := both s f _ _ enabled
    have time := positive_delays s f restart phase valid
    refine ⟨timing ▸ time, ?_⟩
    intro inv member seen
    have included : inv ∈ affected (tcpClauses restart) phase := by
      rw [← catalog]
      exact List.mem_filter.mpr ⟨member, by simp [seen]⟩
    have post : holds (postChecks r phase restart inv) s f = true := by
      rcases partition phase (tcpClauses restart) inv included with tcpMember | linkMember | rfl
      · rw [List.map_inj_left.mp alignment inv tcpMember]
        change (TypedMachine.eval s f (ExprRewrite.run reads inv) && true) = true
        cases restart
        · exact False.elim (List.not_mem_nil tcpMember)
        · have closed := (known s f state tcp).trans (timeWait rfl)
          simp [(tcp_post s f closed).of_mem tcpMember]
      · exact (link_checks s f _ phase linkReady link valid).of_mem linkMember
      · exact OctetBounds.all_sound _ (context s f) packetBound
    rw [obligationsFor_split, timing, holds, List.all_append]
    change (holds (delays restart phase) s f && holds (postChecks r phase restart inv) s f) = true
    simp [time, post]

theorem close_wait_empty : Approved.raw_138_external :=
  certify rule_138 .empty (fixedText e943) false rfl (by intro impossible; cases impossible) rfl
    (by decide +kernel) rfl rfl rfl ⟨⟨by decide +kernel, by decide +kernel, rfl⟩, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩⟩
    (by decide +kernel)

theorem close_wait_pending : Approved.raw_139_external :=
  certify rule_139 .pending (fixedText e943) false rfl (by intro impossible; cases impossible) rfl
    (by decide +kernel) rfl rfl rfl ⟨by decide +kernel, by decide +kernel, rfl⟩
    (by decide +kernel)

theorem close_wait_resolved : Approved.raw_140_external :=
  certify rule_140 .resolved (fixedText e943) false rfl (by intro impossible; cases impossible) rfl
    (by decide +kernel) rfl rfl rfl trivial
    (by decide +kernel)

theorem closing_empty : Approved.raw_141_external :=
  certify rule_141 .empty (fixedText e961) false rfl (by intro impossible; cases impossible) rfl
    (by decide +kernel) rfl rfl rfl ⟨⟨by decide +kernel, by decide +kernel, rfl⟩, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩⟩
    (by decide +kernel)

theorem closing_pending : Approved.raw_142_external :=
  certify rule_142 .pending (fixedText e961) false rfl (by intro impossible; cases impossible) rfl
    (by decide +kernel) rfl rfl rfl ⟨by decide +kernel, by decide +kernel, rfl⟩
    (by decide +kernel)

theorem closing_resolved : Approved.raw_143_external :=
  certify rule_143 .resolved (fixedText e961) false rfl (by intro impossible; cases impossible) rfl
    (by decide +kernel) rfl rfl rfl trivial
    (by decide +kernel)

theorem last_ack_empty : Approved.raw_144_external :=
  certify rule_144 .empty (fixedText e947) false rfl (by intro impossible; cases impossible) rfl
    (by decide +kernel) rfl rfl rfl ⟨⟨by decide +kernel, by decide +kernel, rfl⟩, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩⟩
    (by decide +kernel)

theorem last_ack_pending : Approved.raw_145_external :=
  certify rule_145 .pending (fixedText e947) false rfl (by intro impossible; cases impossible) rfl
    (by decide +kernel) rfl rfl rfl ⟨by decide +kernel, by decide +kernel, rfl⟩
    (by decide +kernel)

theorem last_ack_resolved : Approved.raw_146_external :=
  certify rule_146 .resolved (fixedText e947) false rfl (by intro impossible; cases impossible) rfl
    (by decide +kernel) rfl rfl rfl trivial
    (by decide +kernel)

theorem time_wait_empty : Approved.raw_147_external :=
  certify rule_147 .empty (fixedText e966) true rfl (fun _ => rfl) rfl
    (by decide +kernel) rfl rfl rfl ⟨⟨by decide +kernel, by decide +kernel, rfl⟩, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩⟩
    (by decide +kernel)

theorem time_wait_pending : Approved.raw_148_external :=
  certify rule_148 .pending (fixedText e966) true rfl (fun _ => rfl) rfl
    (by decide +kernel) rfl rfl rfl ⟨by decide +kernel, by decide +kernel, rfl⟩
    (by decide +kernel)

theorem time_wait_resolved : Approved.raw_149_external :=
  certify rule_149 .resolved (fixedText e966) true rfl (fun _ => rfl) rfl
    (by decide +kernel) rfl rfl rfl trivial
    (by decide +kernel)

def firings : List (Rule × Option Nat) :=
  [(rule_138, none), (rule_139, none), (rule_140, none),
   (rule_141, none), (rule_142, none), (rule_143, none),
   (rule_144, none), (rule_145, none), (rule_146, none),
   (rule_147, none), (rule_148, none), (rule_149, none)]

theorem checked : Each (fun p => FiringPreserves model p.1 p.2) firings :=
  ⟨close_wait_empty, close_wait_pending, close_wait_resolved,
   closing_empty, closing_pending, closing_resolved,
   last_ack_empty, last_ack_pending, last_ack_resolved,
   time_wait_empty, time_wait_pending, time_wait_resolved,
   trivial⟩

private theorem finMember (index : Nat) (r : Rule)
    (selected : model.rules[index]? = some r) (external : r.event ∈ model.externalEvents) :
    (r, none) ∈ rawChecks model declaredTimers :=
  raw_external_member model declaredTimers r (List.mem_iff_getElem?.mpr ⟨index, selected⟩) external

theorem members : Each (fun p => p ∈ rawChecks model declaredTimers) firings :=
  ⟨finMember 138 rule_138 rfl (by decide), finMember 139 rule_139 rfl (by decide),
   finMember 140 rule_140 rfl (by decide), finMember 141 rule_141 rfl (by decide),
   finMember 142 rule_142 rfl (by decide), finMember 143 rule_143 rfl (by decide),
   finMember 144 rule_144 rfl (by decide), finMember 145 rule_145 rfl (by decide),
   finMember 146 rule_146 rfl (by decide), finMember 147 rule_147 rfl (by decide),
   finMember 148 rule_148 rfl (by decide), finMember 149 rule_149 rfl (by decide),
   trivial⟩

end TCPIPDuplicateFin
