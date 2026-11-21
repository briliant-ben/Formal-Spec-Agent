import TCPIPClosedCore
namespace TCPIPClosedTransitions
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts
open EffectConditions EffectFootprint TimedObligations TCPIPSendWire GuardedSuffix
set_option maxRecDepth 16384

def resetDelays : LinkPhase → List (Expr .boolean)
  | .empty => [.intGe e10 e44]
  | _ => []

def resetPost (r : Rule) (phase : LinkPhase) (inv : Expr .boolean) : List (Expr .boolean) :=
  (obligationsFor r none [inv]).drop (resetDelays phase).length

def newLinkClauses : LinkPhase → List (Expr .boolean)
  | .empty => [e1594, e1597, e1601, e1604, e1628]
  | _ => []

def resetAffected (clear : Bool) (phase : LinkPhase) : List (Expr .boolean) :=
  (match phase with | .empty => [e1594, e1597, e1601, e1604] | _ => []) ++
    [e1612, e1614, e1615] ++ (match phase with | .empty => [e1628] | _ => []) ++
    phaseClauses ++ (if clear then [e1691, e1692] else []) ++
    [e1698] ++ (if clear then [e1699] else []) ++ [e1704] ++
    (if clear then [e1705] else []) ++ [e1706, e1716, e1721]

theorem resetClassify (clear : Bool) (phase : LinkPhase) (inv : Expr .boolean)
    (included : inv ∈ resetAffected clear phase) :
    inv ∈ affected clear ∨ inv ∈ newLinkClauses phase ∨ inv = e1706 := by
  cases clear <;> cases phase <;> simpa only [resetAffected, affected, newLinkClauses,
    Bool.false_eq_true, ite_false, ite_true, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, false_or, or_assoc, or_left_comm, or_comm] using included

theorem resetQueue (r : Rule) (phase : LinkPhase) (s : Snapshot) (f : Values)
    (valid : invariantsHold model s = true) (enabled : TypedMachine.eval s f (linkGuard phase) = true)
    (ready : linkCondition (resetPost r phase) phase)
    (release : phase = .resolved → TCPIPQueueRelease.queueClauses.map (resetPost r phase) =
      TCPIPQueueRelease.queueClauses.map (fun inv => [ExprRewrite.run TCPIPQueueRelease.releaseReads inv]))
    (inv : Expr .boolean) (member : inv ∈ TCPIPQueueRelease.queueClauses) :
    holds (resetPost r phase inv) s f = true := by
  cases phase
  · apply (link_checks s f _ .empty ready enabled valid).of_mem
    simp only [TCPIPQueueRelease.queueClauses, linkClauses, List.mem_cons, List.not_mem_nil,
      or_false] at member ⊢
    rcases member with a | a | a | a <;> simp [a]
  · exact (link_checks s f _ .pending ready enabled valid).of_mem member
  · rw [List.map_inj_left.mp (release rfl) inv member]
    change (TypedMachine.eval s f (ExprRewrite.run TCPIPQueueRelease.releaseReads inv) && true) = true
    simp [(TCPIPQueueRelease.release_queue_safe s f valid).of_mem member]

theorem resetLink (r : Rule) (phase : LinkPhase) (s : Snapshot) (f : Values)
    (valid : invariantsHold model s = true) (enabled : TypedMachine.eval s f (linkGuard phase) = true)
    (ready : linkCondition (resetPost r phase) phase) (inv : Expr .boolean)
    (member : inv ∈ newLinkClauses phase) : holds (resetPost r phase inv) s f = true := by
  cases phase
  · apply (link_checks s f _ .empty ready enabled valid).of_mem
    simp only [newLinkClauses, linkClauses, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    rcases member with a | a | a | a | a <;> simp [a]
  · exact False.elim (List.not_mem_nil member)
  · exact False.elim (List.not_mem_nil member)

theorem abort_checked (r : Rule) (phase : LinkPhase) (start : String) (clear : Bool)
    (guard : r.guard = .boolAnd (controlGuard start none) (linkGuard phase))
    (timing : obligationsFor r none [] = resetDelays phase)
    (catalog : model.invariants.filter (fun inv => !ignoresFiring inv r none) = resetAffected clear phase)
    (statics : ∀ s f, (staticClauses clear).all (fun inv => holds (resetPost r phase inv) s f) = true)
    (ready : linkCondition (resetPost r phase) phase)
    (release : phase = .resolved → TCPIPQueueRelease.queueClauses.map (resetPost r phase) =
      TCPIPQueueRelease.queueClauses.map (fun inv => [ExprRewrite.run TCPIPQueueRelease.releaseReads inv]))
    (packet : (resetPost r phase e1706).all OctetBounds.certifies = true)
    (buffer : ∀ s f, invariantsHold model s = true → TypedMachine.eval s f (controlGuard start none) = true →
      holds (resetPost r phase e1698) s f = true)
    (window : clear = true → resetPost r phase e1705 = [.intLe (.bytesLength e0) e1221]) :
    FiringPreserves model r none := by
  apply preserves_touched
  intro s f valid _ enabled
  rw [guard] at enabled
  change (TypedMachine.eval s f (controlGuard start none) && TypedMachine.eval s f (linkGuard phase)) = true at enabled
  simp only [Bool.and_eq_true] at enabled
  have positive : holds (resetDelays phase) s f = true := by cases phase <;> rfl
  refine ⟨timing ▸ positive, ?_⟩
  intro inv member seen
  have checked : holds (resetPost r phase inv) s f = true := by
    have includes : inv ∈ resetAffected clear phase := by
      rw [← catalog]
      exact List.mem_filter.mpr ⟨member, by simp [seen]⟩
    rcases resetClassify clear phase inv includes with base | ether | rfl
    · rcases classify clear inv base with queue | static | rfl | ⟨cleared, rfl⟩
      · exact resetQueue r phase s f valid enabled.2 ready release inv queue
      · exact List.all_eq_true.mp (statics s f) _ static
      · exact buffer s f valid enabled.1
      · rw [window cleared]
        have previous : TypedMachine.eval s f e929 ≤ TypedMachine.eval s f e1221 :=
          of_decide_eq_true (List.all_eq_true.mp valid e1705 (by rw [model_invariants]; simp))
        have nonneg : 0 ≤ TypedMachine.eval s f e929 := Int.natCast_nonneg _
        change (decide (0 ≤ TypedMachine.eval s f e1221) && true) = true
        rw [decide_eq_true (Int.le_trans nonneg previous)]
        rfl
    · exact resetLink r phase s f valid enabled.2 ready inv ether
    · exact OctetBounds.all_sound _ (context s f) packet
  rw [obligationsFor_split, timing, holds, List.all_append]
  change (holds (resetDelays phase) s f && holds (resetPost r phase inv) s f) = true
  simp [positive, checked]

theorem reset_buffer_empty (r : Rule) (phase : LinkPhase) (start : String)
    (different : start ≠ fixedText e807)
    (shape : resetPost r phase e1698 = [.implies (.boolNot (.equal .text e14 e807)) e935])
    (s : Snapshot) (f : Values) (valid : invariantsHold model s = true)
    (enabled : TypedMachine.eval s f (controlGuard start none) = true) :
    holds (resetPost r phase e1698) s f = true := by
  rw [shape]
  change (TypedMachine.eval s f e935 && true) = true
  simp [empty_before s f start none different enabled valid]


end TCPIPClosedTransitions
