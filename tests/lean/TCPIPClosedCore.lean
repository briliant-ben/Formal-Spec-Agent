import TCPIPQueueRelease
import TCPIPSendWire
import GuardedSuffix
namespace TCPIPClosedTransitions
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts
open EffectConditions EffectFootprint TimedObligations TCPIPSendWire GuardedSuffix
set_option maxRecDepth 16384

def phaseClauses : List (Expr .boolean) :=
  [e1631, e1634, e1637, e1638, e1639, e1640, e1642, e1644, e1645, e1646, e1647, e1648,
   e1649, e1650, e1651, e1652, e1653, e1654, e1655, e1656, e1657, e1658, e1659,
   e1660, e1661, e1662, e1663, e1664, e1665, e1666, e1667, e1669, e1679, e1685,
   e1687, e1690]

def staticClauses (clear : Bool) :=
  phaseClauses ++ (if clear then [e1691, e1692, e1699] else []) ++ [e1704, e1716]

def affected (clear : Bool) : List (Expr .boolean) :=
  [e1612, e1614, e1615] ++ phaseClauses ++ (if clear then [e1691, e1692] else []) ++
    [e1698] ++ (if clear then [e1699] else []) ++ [e1704] ++
    (if clear then [e1705] else []) ++ [e1716, e1721]

theorem classify (clear : Bool) (inv : Expr .boolean) (included : inv ∈ affected clear) :
    inv ∈ TCPIPQueueRelease.queueClauses ∨ inv ∈ staticClauses clear ∨
      inv = e1698 ∨ (clear = true ∧ inv = e1705) := by
  cases clear <;> simpa only [affected, staticClauses, TCPIPQueueRelease.queueClauses,
    Bool.false_eq_true, ite_false, ite_true, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, false_or, false_and, true_and, or_assoc, or_left_comm, or_comm] using included

theorem close_checked (r : Rule) (firing : Option Nat) (clear : Bool)
    (total : obligationsFor r firing [] = [])
    (catalog : model.invariants.filter (fun inv => !ignoresFiring inv r firing) = affected clear)
    (statics : ∀ s f, (staticClauses clear).all (fun inv => holds (obligationsFor r firing [inv]) s f) = true)
    (bind : TCPIPQueueRelease.queueClauses.map (fun inv => obligationsFor r firing [inv]) =
      TCPIPQueueRelease.queueClauses.map (fun inv => [ExprRewrite.run TCPIPQueueRelease.releaseReads inv]))
    (buffer : ∀ s f, invariantsHold model s = true → TypedMachine.eval s f r.guard = true →
      holds (obligationsFor r firing [e1698]) s f = true)
    (window : clear = true → obligationsFor r firing [e1705] = [.intLe (.bytesLength e0) e1221]) :
    FiringPreserves model r firing := by
  apply preserves_touched
  intro s f valid _ enabled
  refine ⟨total.symm ▸ rfl, ?_⟩
  intro inv member seen
  have includes : inv ∈ affected clear := by
    rw [← catalog]
    exact List.mem_filter.mpr ⟨member, by simp [seen]⟩
  rcases classify clear inv includes with queue | static | rfl | ⟨cleared, rfl⟩
  · rw [List.map_inj_left.mp bind inv queue]
    change (TypedMachine.eval s f (ExprRewrite.run TCPIPQueueRelease.releaseReads inv) && true) = true
    simp [(TCPIPQueueRelease.release_queue_safe s f valid).of_mem queue]
  · exact List.all_eq_true.mp (statics s f) _ static
  · exact buffer s f valid enabled
  · rw [window cleared]
    have previous : TypedMachine.eval s f e929 ≤ TypedMachine.eval s f e1221 :=
      of_decide_eq_true (List.all_eq_true.mp valid e1705 (by rw [model_invariants]; simp))
    have nonneg : 0 ≤ TypedMachine.eval s f e929 := Int.natCast_nonneg _
    change (decide (0 ≤ TypedMachine.eval s f e1221) && true) = true
    rw [decide_eq_true (Int.le_trans nonneg previous)]
    rfl

def controlGuard (start : String) (frameFilter : Option (Expr .boolean)) : Expr .boolean :=
  let atPhase := Expr.equal .text e488 (.literal .text start)
  match frameFilter with
  | none => .boolAnd atPhase e3
  | some select => .boolAnd (.boolAnd atPhase select) e721

theorem empty_before (s : Snapshot) (f : Values) (start : String) (frameFilter : Option (Expr .boolean))
    (different : start ≠ TypedMachine.eval initial zeroValues e807)
    (enabled : TypedMachine.eval s f (controlGuard start frameFilter) = true)
    (valid : invariantsHold model s = true) :
    TypedMachine.eval s f e935 = true := by
  have phase : TypedMachine.eval s f e488 = start := by
    cases frameFilter with
    | none =>
      change (decide (TypedMachine.eval s f e488 = start) && true) = true at enabled
      simp only [Bool.and_eq_true] at enabled
      exact of_decide_eq_true enabled.1
    | some select =>
      change ((decide (TypedMachine.eval s f e488 = start) && TypedMachine.eval s f select) &&
        TypedMachine.eval s f e721) = true at enabled
      simp only [Bool.and_eq_true] at enabled
      exact of_decide_eq_true enabled.1.1
  have noData : TypedMachine.eval s zeroValues e923 = false := by
    change decide (TypedMachine.eval s f e488 = TypedMachine.eval s f e807) = false
    exact decide_eq_false (phase ▸ different)
  have before := List.all_eq_true.mp valid e1698 (by rw [model_invariants]; simp)
  change (!(!TypedMachine.eval s zeroValues e923) || TypedMachine.eval s zeroValues e935) = true at before
  simp only [noData, Bool.not_false, Bool.not_true, Bool.false_or] at before
  exact before

theorem preserve_empty (r : Rule) (firing : Option Nat) (start : String)
    (frameFilter : Option (Expr .boolean))
    (guard : r.guard = controlGuard start frameFilter)
    (different : start ≠ TypedMachine.eval initial zeroValues e807)
    (before : obligationsFor r firing [e1698] = [.implies (.boolNot (.equal .text e14 e807)) e935])
    (s : Snapshot) (f : Values) (valid : invariantsHold model s = true)
    (enabled : TypedMachine.eval s f r.guard = true) :
    holds (obligationsFor r firing [e1698]) s f = true := by
  rw [guard] at enabled
  rw [before]
  change (TypedMachine.eval s f e935 && true) = true
  simp [empty_before s f start frameFilter different enabled valid]

abbrev fixedText (e : Expr .text) := TypedMachine.eval initial zeroValues e


end TCPIPClosedTransitions
