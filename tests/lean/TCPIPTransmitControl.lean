import TCPIPTransmitLayout

namespace TCPIPTransmit
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts TCPIPTransmitFacts
open EffectConditions EffectFootprint GuardedSuffix TimedObligations TCPIPSendWire
set_option maxRecDepth 16384

theorem timer_checks (s : Snapshot) (f : Values)
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

theorem other_control (s : Snapshot) (f : Values)
    (established : TypedMachine.eval s f e923 = true) :
    TypedMachine.eval s f e1674 = false ∧ TypedMachine.eval s f e1702 = false := by
  have state : s.values.texts 56 = TypedMachine.eval initial zeroValues e807 :=
    of_decide_eq_true established
  simp only [e1674, e1673, e1672, e1671, e1670, e1702, e1701, e1700,
    e743, e810, e955, e962, e964, e944, e959, e967, e488, TypedMachine.eval,
    TypedIR.eval, context, getValue, state]
  exact ⟨rfl, rfl⟩

theorem append_checked {xs ys : List α} {holds : α → Prop}
    (left : Each holds xs) (right : Each holds ys) : Each holds (xs ++ ys) := by
  induction xs with
  | nil => exact right
  | cons _ _ ih => exact ⟨left.1, ih left.2⟩

theorem tcp_post (s : Snapshot) (f : Values) (first : Bool)
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

theorem tcp_checks (s : Snapshot) (f : Values) (first : Bool) (phase : LinkPhase)
    (align : (tcpClauses first).map (postChecks first phase) =
      (tcpClauses first).map (fun inv => [ExprRewrite.run (reads first) inv]))
    (valid : invariantsHold model s = true) (enabled : TypedMachine.eval s f (transmitGuard first) = true)
    (inv : Expr .boolean) (member : inv ∈ tcpClauses first) : Post s f first phase inv := by
  unfold Post
  rw [List.map_inj_left.mp align inv member]
  change (TypedMachine.eval s f (ExprRewrite.run (reads first) inv) && true) = true
  simp [(tcp_post s f first valid enabled).of_mem member]


end TCPIPTransmit
