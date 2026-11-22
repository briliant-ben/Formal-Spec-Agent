import InvariantFootprint

namespace FormalSpecAgent.ResetPreservation

open TypedIR TypedMachine TypedContracts TypedFiringContracts TimedObligations InvariantFootprint

private def emptyAt (slot : Nat) : Expr .boolean :=
  .equal .integer (.bytesLength (.variable .octets slot)) (.literal .integer 0)

/-- Recognize invariants whose truth follows from a zero length at this slot. -/
private def followsFromEmpty (slot : Nat) : Expr .boolean → Bool
  | .intLe (.bytesLength (.variable .octets index)) (.literal .integer upper) =>
      index == slot && decide (0 ≤ upper)
  | .implies _ (.equal .integer (.bytesLength (.variable .octets index)) (.literal .integer n)) =>
      index == slot && n == 0
  | _ => false

private theorem empty_length (slot : Nat) (snapshot : Snapshot)
    (empty : eval snapshot zeroValues (emptyAt slot) = true) :
    (getValue .octets snapshot.values slot).length = 0 := by
  have h : (Int.ofNat (getValue .octets snapshot.values slot).length) = 0 :=
    of_decide_eq_true empty
  exact Int.ofNat_inj.mp h

private theorem empty_implies (slot : Nat) (snapshot : Snapshot) (inv : Expr .boolean)
    (empty : eval snapshot zeroValues (emptyAt slot) = true)
    (implied : followsFromEmpty slot inv = true) :
    eval snapshot zeroValues inv = true := by
  have length := empty_length slot snapshot empty
  unfold followsFromEmpty at implied
  split at implied
  next index upper =>
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at implied
    obtain ⟨same, upperBound⟩ := implied
    subst index
    change decide (Int.ofNat (getValue .octets snapshot.values slot).length ≤ upper) = true
    rw [length]
    exact decide_eq_true upperBound
  next premise index n =>
    simp only [Bool.and_eq_true, beq_iff_eq] at implied
    obtain ⟨same, zero⟩ := implied
    subst index
    subst n
    change ((!eval snapshot zeroValues premise) ||
      decide (Int.ofNat (getValue .octets snapshot.values slot).length = 0)) = true
    rw [length]
    simp
  next => contradiction

private def resetStore (snapshot : Snapshot) (slot : Nat) : Snapshot :=
  { snapshot with values := setValue .octets slot [] snapshot.values }

/-- The temporary model keeps unaffected invariants and explicitly tracks
that the reset buffer stays empty through the remaining original actions. -/
private def afterReset (model : Model) (slot : Nat) : Model :=
  { model with invariants := emptyAt slot :: model.invariants.filter (ignoresSlot slot) }

private theorem reset_starts_valid (model : Model) (snapshot : Snapshot) (slot : Nat)
    (valid : invariantsHold model snapshot = true) :
    invariantsHold (afterReset model slot) (resetStore snapshot slot) = true := by
  apply List.all_eq_true.mpr
  intro inv member
  change inv ∈ emptyAt slot :: model.invariants.filter (ignoresSlot slot) at member
  rcases List.mem_cons.mp member with same | rest
  · rw [same]
    simp [resetStore, emptyAt, TypedMachine.eval, context, TypedIR.eval, getValue, setValue, equalValue]
  · obtain ⟨oldMember, ignores⟩ := List.mem_filter.mp rest
    exact (eval_after_unrelated_set inv (context snapshot zeroValues) .octets slot [] ignores).trans
      (List.all_eq_true.mp valid inv oldMember)

private theorem reset_restores_valid (model : Model) (snapshot : Snapshot) (slot : Nat)
    (classified : model.invariants.all (fun inv => ignoresSlot slot inv || followsFromEmpty slot inv) = true)
    (valid : invariantsHold (afterReset model slot) snapshot = true) :
    invariantsHold model snapshot = true := by
  apply List.all_eq_true.mpr
  intro inv member
  have allowed := List.all_eq_true.mp classified inv member
  simp only [Bool.or_eq_true] at allowed
  rcases allowed with unchanged | implied
  · exact List.all_eq_true.mp valid inv (List.mem_cons_of_mem _
      (List.mem_filter.mpr ⟨member, unchanged⟩))
  · exact empty_implies slot snapshot inv (List.all_eq_true.mp valid _ (by simp [afterReset])) implied

private theorem preserve_reset (model : Model) (rule : Rule) (slot : Nat) (rest : List Action)
    (actions : rule.actions = .assign .octets slot (.literal .octets []) :: rest)
    (loop : rule.target = rule.source)
    (guardUntouched : ignoresSlot slot rule.guard = true)
    (classified : model.invariants.all (fun inv => ignoresSlot slot inv || followsFromEmpty slot inv) = true)
    (safe : rest.all (guardedEffect (afterReset model slot) rule.guard) = true) :
    FiringPreserves model rule none := by
  intro snapshot fields valid source enabled
  let tailRule := { rule with actions := rest }
  have tailEnabled : eval (resetStore snapshot slot) fields tailRule.guard = true :=
    (eval_after_unrelated_set rule.guard (context snapshot fields) .octets slot [] guardUntouched).trans
      enabled
  obtain ⟨transition, executed, afterValid⟩ :=
    external_rule_guarded_invariants (afterReset model slot) tailRule loop safe
      (resetStore snapshot slot) fields (reset_starts_valid model snapshot slot valid) source tailEnabled
  refine ⟨transition, ?_, reset_restores_valid model transition.after slot classified afterValid⟩
  unfold candidate
  rw [actions]
  exact executed

private def acceptsActions (model : Model) (rule : Rule) : List Action → Bool
  | .assign .octets slot (.literal .octets []) :: rest =>
      ignoresSlot slot rule.guard &&
      model.invariants.all (fun inv => ignoresSlot slot inv || followsFromEmpty slot inv) &&
      rest.all (guardedEffect (afterReset model slot) rule.guard)
  | _ => false

private def acceptsReset (model : Model) (pair : Rule × Option Nat) : Bool :=
  pair.2.isNone && (pair.1.target == pair.1.source) && acceptsActions model pair.1 pair.1.actions

/-- Subset of the original raw obligations covered by a leading buffer reset. -/
def resetChecks (model : Model) (ids : List Nat) : List (Rule × Option Nat) :=
  (rawChecks model ids).filter (acceptsReset model)

theorem resetChecks_sound (model : Model) (ids : List Nat) :
    Each (fun pairing => FiringPreserves model pairing.1 pairing.2) (resetChecks model ids) := by
  generalize h : resetChecks model ids = checks
  suffices ∀ p ∈ checks, FiringPreserves model p.1 p.2 by
    clear h
    induction checks with
    | nil => trivial
    | cons p rest ih =>
      exact ⟨this p (by simp), ih (fun q member => this q (List.mem_cons_of_mem _ member))⟩
  intro ⟨rule, trigger⟩ member
  have accepted := (List.mem_filter.mp (h ▸ member)).2
  cases trigger with
  | some _ => contradiction
  | none =>
    simp only [acceptsReset, Option.isNone, Bool.true_and, Bool.and_eq_true, beq_iff_eq] at accepted
    obtain ⟨loop, actions⟩ := accepted
    unfold acceptsActions at actions
    split at actions
    next slot rest shape =>
      simp only [Bool.and_eq_true] at actions
      exact preserve_reset model rule slot rest shape loop actions.1.1 actions.1.2 actions.2
    next => contradiction

end FormalSpecAgent.ResetPreservation
