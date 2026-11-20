import TCPIPQueueRelease
namespace TCPIPClosedControl
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts
open EffectConditions EffectFootprint TimedObligations
set_option maxRecDepth 16384

private def phaseClauses : List (Expr .boolean) :=
  [e1631, e1634, e1637, e1638, e1639, e1640, e1642, e1644, e1645, e1646, e1647, e1648,
   e1649, e1650, e1651, e1652, e1653, e1654, e1655, e1656, e1657, e1658, e1659,
   e1660, e1661, e1662, e1663, e1664, e1665, e1666, e1667, e1669, e1679, e1685,
   e1687, e1690]

private def staticClauses := phaseClauses ++ [e1704, e1716]

private def affected : List (Expr .boolean) :=
  [e1612, e1614, e1615] ++ phaseClauses ++ [e1698, e1704, e1716, e1721]

private def controlGuard (start : String) : Expr .boolean :=
  .boolAnd (.equal .text e488 (.literal .text start)) e3

private theorem empty_before (s : Snapshot) (f : Values) (start : String)
    (different : start ≠ TypedMachine.eval s f e807)
    (enabled : TypedMachine.eval s f (controlGuard start) = true)
    (valid : invariantsHold model s = true) :
    TypedMachine.eval s f e935 = true := by
  have phase : TypedMachine.eval s f e488 = start := by
    change (decide (TypedMachine.eval s f e488 = start) && true) = true at enabled
    simp only [Bool.and_eq_true] at enabled
    exact of_decide_eq_true enabled.1
  have noData : TypedMachine.eval s zeroValues e923 = false := by
    change decide (TypedMachine.eval s f e488 = TypedMachine.eval s f e807) = false
    exact decide_eq_false (phase ▸ different)
  have before := List.all_eq_true.mp valid e1698 (by rw [model_invariants]; simp)
  change (!(!TypedMachine.eval s zeroValues e923) || TypedMachine.eval s zeroValues e935) = true at before
  simp only [noData, Bool.not_false, Bool.not_true, Bool.false_or] at before
  exact before

private def closed (reason : Expr .text) : List Action :=
  [.assign .octets 16 e951, .assign .text 57 e952, .cancel 2, .cancel 4, .cancel 3,
   .emit 6 [⟨0, .text, reason⟩], .assign .text 56 e14]

private theorem close_checked (r : Rule) (reason : Expr .text) (start : String)
    (guard : r.guard = controlGuard start)
    (different : start ≠ TypedMachine.eval initial zeroValues e807)
    (shape : r.actions = closed reason)
    (catalog : model.invariants.filter (fun inv => !ignoresFiring inv r none) = affected)
    (statics : ∀ s f, (staticClauses.map (fun inv => holds (obligationsFor r none [inv]) s f)).all id = true)
    (bind : TCPIPQueueRelease.queueClauses.map (fun inv => obligationsFor r none [inv]) =
      TCPIPQueueRelease.queueClauses.map (fun inv => [ExprRewrite.run TCPIPQueueRelease.releaseReads inv]))
    (buffer : obligationsFor r none [e1698] =
      [.implies (.boolNot (.equal .text e14 e807)) e935]) :
    FiringPreserves model r none := by
  apply preserves_touched
  intro s f valid _ enabled
  have total : holds (obligationsFor r none []) s f = true := by
    change holds (obligationsFor r none []) s f = true
    simp only [obligationsFor, shape]
    rfl
  refine ⟨total, ?_⟩
  intro inv member seen
  have includes : inv ∈ affected := by
    rw [← catalog]
    exact List.mem_filter.mpr ⟨member, by simp [seen]⟩
  have cases : inv ∈ TCPIPQueueRelease.queueClauses ∨ inv ∈ staticClauses ∨ inv = e1698 := by
    simpa only [affected, staticClauses, TCPIPQueueRelease.queueClauses, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false, or_assoc, or_left_comm, or_comm] using includes
  rcases cases with queue | static | rfl
  · rw [List.map_inj_left.mp bind inv queue]
    change (TypedMachine.eval s f (ExprRewrite.run TCPIPQueueRelease.releaseReads inv) && true) = true
    simp [(TCPIPQueueRelease.release_queue_safe s f valid).of_mem queue]
  · exact List.all_eq_true.mp (statics s f) _ (List.mem_map.mpr ⟨inv, static, rfl⟩)
  · rw [guard] at enabled
    rw [buffer]
    change (TypedMachine.eval s f e935 && true) = true
    simp [empty_before s f start different enabled valid]

theorem close_listen : Approved.raw_111_external :=
  close_checked rule_111 e953 (TypedMachine.eval initial zeroValues e579)
    rfl (by decide) rfl rfl (fun _ _ => rfl) rfl rfl

theorem close_syn_sent : Approved.raw_112_external :=
  close_checked rule_112 e953 (TypedMachine.eval initial zeroValues e568)
    rfl (by decide) rfl rfl (fun _ _ => rfl) rfl rfl

theorem abort_closed : Approved.raw_172_external :=
  close_checked rule_172 e1062 (TypedMachine.eval initial zeroValues e14)
    rfl (by decide) rfl rfl (fun _ _ => rfl) rfl rfl

theorem abort_listen : Approved.raw_173_external :=
  close_checked rule_173 e1062 (TypedMachine.eval initial zeroValues e579)
    rfl (by decide) rfl rfl (fun _ _ => rfl) rfl rfl

theorem abort_syn_sent : Approved.raw_174_external :=
  close_checked rule_174 e1062 (TypedMachine.eval initial zeroValues e568)
    rfl (by decide) rfl rfl (fun _ _ => rfl) rfl rfl

theorem abort_closing : Approved.raw_190_external :=
  close_checked rule_190 e1062 (TypedMachine.eval initial zeroValues e961)
    rfl (by decide) rfl rfl (fun _ _ => rfl) rfl rfl

theorem abort_last_ack : Approved.raw_191_external :=
  close_checked rule_191 e1062 (TypedMachine.eval initial zeroValues e947)
    rfl (by decide) rfl rfl (fun _ _ => rfl) rfl rfl

theorem abort_time_wait : Approved.raw_192_external :=
  close_checked rule_192 e1062 (TypedMachine.eval initial zeroValues e966)
    rfl (by decide) rfl rfl (fun _ _ => rfl) rfl rfl

def firings : List (Rule × Option Nat) :=
  [(rule_111, none), (rule_112, none), (rule_172, none), (rule_173, none),
   (rule_174, none), (rule_190, none), (rule_191, none), (rule_192, none)]

theorem checked : Each (fun p => FiringPreserves model p.1 p.2) firings :=
  ⟨close_listen, close_syn_sent, abort_closed, abort_listen, abort_syn_sent, abort_closing,
   abort_last_ack, abort_time_wait, trivial⟩

private theorem controlMember (index : Nat) (r : Rule)
    (selected : model.rules[index]? = some r) (external : r.event ∈ model.externalEvents) :
    (r, none) ∈ rawChecks model declaredTimers :=
  raw_external_member model declaredTimers r (List.mem_iff_getElem?.mpr ⟨index, selected⟩) external

theorem members : Each (fun p => p ∈ rawChecks model declaredTimers) firings :=
  ⟨controlMember 111 rule_111 rfl (by decide), controlMember 112 rule_112 rfl (by decide),
   controlMember 172 rule_172 rfl (by decide), controlMember 173 rule_173 rfl (by decide),
   controlMember 174 rule_174 rfl (by decide), controlMember 190 rule_190 rfl (by decide),
   controlMember 191 rule_191 rfl (by decide), controlMember 192 rule_192 rfl (by decide), trivial⟩

end TCPIPClosedControl
