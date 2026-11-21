import TCPIPTransmitControl
import TCPIPTransmitLink

namespace TCPIPTransmit
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts TCPIPTransmitFacts
open EffectConditions EffectFootprint GuardedSuffix TimedObligations TCPIPSendWire
set_option maxRecDepth 16384

theorem certify (first : Bool) (phase : LinkPhase)
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


end TCPIPTransmit
