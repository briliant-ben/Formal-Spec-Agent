import TCPIPQueueRelease
namespace TCPIPClosedTransitions
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts
open EffectConditions EffectFootprint TimedObligations
set_option maxRecDepth 16384

private def phaseClauses : List (Expr .boolean) :=
  [e1631, e1634, e1637, e1638, e1639, e1640, e1642, e1644, e1645, e1646, e1647, e1648,
   e1649, e1650, e1651, e1652, e1653, e1654, e1655, e1656, e1657, e1658, e1659,
   e1660, e1661, e1662, e1663, e1664, e1665, e1666, e1667, e1669, e1679, e1685,
   e1687, e1690]

private def staticClauses (clear : Bool) :=
  phaseClauses ++ (if clear then [e1691, e1692, e1699] else []) ++ [e1704, e1716]

private def affected (clear : Bool) : List (Expr .boolean) :=
  [e1612, e1614, e1615] ++ phaseClauses ++ (if clear then [e1691, e1692] else []) ++
    [e1698] ++ (if clear then [e1699] else []) ++ [e1704] ++
    (if clear then [e1705] else []) ++ [e1716, e1721]

private theorem classify (clear : Bool) (inv : Expr .boolean) (included : inv ∈ affected clear) :
    inv ∈ TCPIPQueueRelease.queueClauses ∨ inv ∈ staticClauses clear ∨
      inv = e1698 ∨ (clear = true ∧ inv = e1705) := by
  cases clear <;> simpa only [affected, staticClauses, TCPIPQueueRelease.queueClauses,
    Bool.false_eq_true, ite_false, ite_true, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, false_or, false_and, true_and, or_assoc, or_left_comm, or_comm] using included

private theorem close_checked (r : Rule) (firing : Option Nat) (clear : Bool)
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

private def controlGuard (start : String) (frameFilter : Option (Expr .boolean)) : Expr .boolean :=
  let atPhase := Expr.equal .text e488 (.literal .text start)
  match frameFilter with
  | none => .boolAnd atPhase e3
  | some select => .boolAnd (.boolAnd atPhase select) e721

private theorem empty_before (s : Snapshot) (f : Values) (start : String) (frameFilter : Option (Expr .boolean))
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

private theorem preserve_empty (r : Rule) (firing : Option Nat) (start : String)
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

private abbrev fixedText (e : Expr .text) := TypedMachine.eval initial zeroValues e

theorem close_111 : Approved.raw_111_external :=
  close_checked rule_111 none false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_111 none (fixedText e579) none rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_112 : Approved.raw_112_external :=
  close_checked rule_112 none false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_112 none (fixedText e568) none rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_165 : Approved.raw_165_timer_4 :=
  close_checked rule_165 (some 4) false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_165 (some 4) (fixedText e568) none rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_166 : Approved.raw_166_timer_4 :=
  close_checked rule_166 (some 4) false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_166 (some 4) (fixedText e740) none rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_167 : Approved.raw_167_timer_4 :=
  close_checked rule_167 (some 4) false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_167 (some 4) (fixedText e940) none rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_168 : Approved.raw_168_timer_4 :=
  close_checked rule_168 (some 4) false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_168 (some 4) (fixedText e958) none rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_169 : Approved.raw_169_timer_4 :=
  close_checked rule_169 (some 4) false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_169 (some 4) (fixedText e961) none rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_170 : Approved.raw_170_timer_4 :=
  close_checked rule_170 (some 4) false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_170 (some 4) (fixedText e947) none rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_171 : Approved.raw_171_timer_3 :=
  close_checked rule_171 (some 3) false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_171 (some 3) (fixedText e966) none rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_172 : Approved.raw_172_external :=
  close_checked rule_172 none false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_172 none (fixedText e14) none rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_173 : Approved.raw_173_external :=
  close_checked rule_173 none false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_173 none (fixedText e579) none rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_174 : Approved.raw_174_external :=
  close_checked rule_174 none false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_174 none (fixedText e568) none rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_190 : Approved.raw_190_external :=
  close_checked rule_190 none false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_190 none (fixedText e961) none rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_191 : Approved.raw_191_external :=
  close_checked rule_191 none false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_191 none (fixedText e947) none rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_192 : Approved.raw_192_external :=
  close_checked rule_192 none false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_192 none (fixedText e966) none rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_197 : Approved.raw_197_external :=
  close_checked rule_197 none false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_197 none (fixedText e740) (some e1093) rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_198 : Approved.raw_198_external :=
  close_checked rule_198 none true rfl rfl (fun _ _ => rfl) rfl
    (fun _ _ _ _ => rfl) (fun _ => rfl)

theorem close_199 : Approved.raw_199_external :=
  close_checked rule_199 none false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_199 none (fixedText e940) (some e1097) rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_200 : Approved.raw_200_external :=
  close_checked rule_200 none false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_200 none (fixedText e958) (some e1097) rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_201 : Approved.raw_201_external :=
  close_checked rule_201 none false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_201 none (fixedText e943) (some e1097) rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_202 : Approved.raw_202_external :=
  close_checked rule_202 none false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_202 none (fixedText e961) (some e1097) rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_203 : Approved.raw_203_external :=
  close_checked rule_203 none false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_203 none (fixedText e947) (some e1097) rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_204 : Approved.raw_204_external :=
  close_checked rule_204 none false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_204 none (fixedText e966) (some e1097) rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_207 : Approved.raw_207_external :=
  close_checked rule_207 none false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_207 none (fixedText e568) (some e1120) rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_209 : Approved.raw_209_external :=
  close_checked rule_209 none false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_209 none (fixedText e740) (some e1126) rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_210 : Approved.raw_210_external :=
  close_checked rule_210 none true rfl rfl (fun _ _ => rfl) rfl
    (fun _ _ _ _ => rfl) (fun _ => rfl)

theorem close_211 : Approved.raw_211_external :=
  close_checked rule_211 none false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_211 none (fixedText e940) (some e1129) rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_212 : Approved.raw_212_external :=
  close_checked rule_212 none false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_212 none (fixedText e958) (some e1129) rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_213 : Approved.raw_213_external :=
  close_checked rule_213 none false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_213 none (fixedText e943) (some e1129) rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_214 : Approved.raw_214_external :=
  close_checked rule_214 none false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_214 none (fixedText e961) (some e1129) rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_215 : Approved.raw_215_external :=
  close_checked rule_215 none false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_215 none (fixedText e947) (some e1129) rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_216 : Approved.raw_216_external :=
  close_checked rule_216 none false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_216 none (fixedText e966) (some e1129) rfl (by decide) rfl)
    (by intro impossible; cases impossible)

def firings : List (Rule × Option Nat) :=
  [(rule_111, none), (rule_112, none), (rule_165, some 4),
   (rule_166, some 4), (rule_167, some 4), (rule_168, some 4),
   (rule_169, some 4), (rule_170, some 4), (rule_171, some 3),
   (rule_172, none), (rule_173, none), (rule_174, none),
   (rule_190, none), (rule_191, none), (rule_192, none),
   (rule_197, none), (rule_198, none), (rule_199, none),
   (rule_200, none), (rule_201, none), (rule_202, none),
   (rule_203, none), (rule_204, none), (rule_207, none),
   (rule_209, none), (rule_210, none), (rule_211, none),
   (rule_212, none), (rule_213, none), (rule_214, none),
   (rule_215, none), (rule_216, none)]

theorem checked : Each (fun p => FiringPreserves model p.1 p.2) firings :=
  ⟨close_111, close_112, close_165, close_166, close_167, close_168,
   close_169, close_170, close_171, close_172, close_173, close_174,
   close_190, close_191, close_192, close_197, close_198, close_199,
   close_200, close_201, close_202, close_203, close_204, close_207,
   close_209, close_210, close_211, close_212, close_213, close_214,
   close_215, close_216, trivial⟩

private theorem externalMember (index : Nat) (r : Rule)
    (selected : model.rules[index]? = some r) (external : r.event ∈ model.externalEvents) :
    (r, none) ∈ rawChecks model declaredTimers :=
  raw_external_member model declaredTimers r (List.mem_iff_getElem?.mpr ⟨index, selected⟩) external

private theorem timerMember (index : Nat) (r : Rule) (timer : Nat)
    (selected : model.rules[index]? = some r) (declared : timer ∈ declaredTimers)
    (trigger : r.event = model.timerEvents timer) : (r, some timer) ∈ rawChecks model declaredTimers :=
  raw_timer_member model declaredTimers r timer (List.mem_iff_getElem?.mpr ⟨index, selected⟩) declared trigger

theorem members : Each (fun p => p ∈ rawChecks model declaredTimers) firings :=
  ⟨externalMember 111 rule_111 rfl (by decide), externalMember 112 rule_112 rfl (by decide),
   timerMember 165 rule_165 4 rfl (by decide) rfl, timerMember 166 rule_166 4 rfl (by decide) rfl,
   timerMember 167 rule_167 4 rfl (by decide) rfl, timerMember 168 rule_168 4 rfl (by decide) rfl,
   timerMember 169 rule_169 4 rfl (by decide) rfl, timerMember 170 rule_170 4 rfl (by decide) rfl,
   timerMember 171 rule_171 3 rfl (by decide) rfl, externalMember 172 rule_172 rfl (by decide),
   externalMember 173 rule_173 rfl (by decide), externalMember 174 rule_174 rfl (by decide),
   externalMember 190 rule_190 rfl (by decide), externalMember 191 rule_191 rfl (by decide),
   externalMember 192 rule_192 rfl (by decide), externalMember 197 rule_197 rfl (by decide),
   externalMember 198 rule_198 rfl (by decide), externalMember 199 rule_199 rfl (by decide),
   externalMember 200 rule_200 rfl (by decide), externalMember 201 rule_201 rfl (by decide),
   externalMember 202 rule_202 rfl (by decide), externalMember 203 rule_203 rfl (by decide),
   externalMember 204 rule_204 rfl (by decide), externalMember 207 rule_207 rfl (by decide),
   externalMember 209 rule_209 rfl (by decide), externalMember 210 rule_210 rfl (by decide),
   externalMember 211 rule_211 rfl (by decide), externalMember 212 rule_212 rfl (by decide),
   externalMember 213 rule_213 rfl (by decide), externalMember 214 rule_214 rfl (by decide),
   externalMember 215 rule_215 rfl (by decide), externalMember 216 rule_216 rfl (by decide),
   trivial⟩

end TCPIPClosedTransitions
