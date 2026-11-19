import TypedFiringContracts

namespace FormalSpecAgent.InvariantFootprint

open TypedIR TypedMachine TypedContracts TypedFiringContracts

/-- Test whether evaluation can depend on a given store slot.
Event slots, the state, and timer IDs are separate namespaces. -/
def ignoresSlot (slot : Nat) {kind : Kind} (expr : Expr kind) : Bool :=
  match expr with
  | .variable _ index => slot != index
  | .literal _ _ | .field _ _ | .stateIs _ | .timerActive _ => true
  | .equal _ l r | .notEqual _ l r =>
    ignoresSlot slot l && ignoresSlot slot r
  | .choose _ cond l r =>
    ignoresSlot slot cond && ignoresSlot slot l && ignoresSlot slot r
  | .boolAnd l r | .boolOr l r | .implies l r =>
    ignoresSlot slot l && ignoresSlot slot r
  | .add l r | .mul l r | .sub l r | .minimum l r | .intLe l r | .intGe l r =>
    ignoresSlot slot l && ignoresSlot slot r
  | .seqAdd l r => ignoresSlot slot l && ignoresSlot slot r
  | .seqDistance l r | .seqComparable l r | .seqLt l r | .seqLe l r =>
    ignoresSlot slot l && ignoresSlot slot r
  | .concat l r => ignoresSlot slot l && ignoresSlot slot r
  | .byteAt buf i => ignoresSlot slot buf && ignoresSlot slot i
  | .slice buf i count => ignoresSlot slot buf && ignoresSlot slot i && ignoresSlot slot count
  | .boolNot expr | .bytesLength expr | .checksum expr => ignoresSlot slot expr
  | .pack8 expr | .pack16 expr | .pack32 expr => ignoresSlot slot expr

theorem getValue_after_unrelated_set (readKind writeKind : Kind) (readSlot writeSlot : Nat)
    (source : Values) (value : Value writeKind) (different : readSlot ≠ writeSlot) :
    getValue readKind (setValue writeKind writeSlot value source) readSlot =
      getValue readKind source readSlot := by
  cases readKind <;> cases writeKind <;> simp [getValue, setValue, different]

theorem eval_after_unrelated_set {kind : Kind} (expr : Expr kind) (ctx : Context)
    (writeKind : Kind) (slot : Nat) (value : Value writeKind)
    (untouched : ignoresSlot slot expr = true) :
    TypedIR.eval expr { ctx with store := setValue writeKind slot value ctx.store } =
      TypedIR.eval expr ctx := by
  induction expr with
  | «variable» kind index =>
    simp only [ignoresSlot, bne_iff_ne] at untouched
    exact getValue_after_unrelated_set kind writeKind index slot ctx.store value (Ne.symm untouched)
  | _ => simp_all [ignoresSlot, TypedIR.eval, Bool.and_eq_true]

theorem invariant_after_unrelated_set (model : Model) (snapshot : Snapshot) (slot : Nat)
    (writeKind : Kind) (value : Value writeKind)
    (unrelated : model.invariants.all (ignoresSlot slot) = true)
    (valid : invariantsHold model snapshot = true) :
    invariantsHold model { snapshot with values := setValue writeKind slot value snapshot.values } = true := by
  apply List.all_eq_true.mpr
  intro inv member
  unfold TypedMachine.eval
  have untouched := List.all_eq_true.mp unrelated inv member
  exact (eval_after_unrelated_set inv (context snapshot zeroValues) writeKind slot value untouched).trans
    (List.all_eq_true.mp valid inv member)

/-- Effects that are total and leave all invariant inputs and timer state intact. -/
def keepsInvariants (model : Model) : Action → Bool
  | .assign _ slot _ => model.invariants.all (ignoresSlot slot)
  | .emit _ _ => true
  | .arm _ _ | .cancel _ => false

theorem work_keeps_invariants (model : Model) (actions : List Action) (snapshot : Snapshot)
    (fields : Values) (out : List Message)
    (noChanges : actions.all (keepsInvariants model) = true)
    (valid : invariantsHold model snapshot = true) :
    ∃ after emitted, work actions snapshot fields out = .ok (after, emitted) ∧
      after.state = snapshot.state ∧ invariantsHold model after = true := by
  induction actions generalizing snapshot out with
  | nil => exact ⟨snapshot, out, rfl, rfl, valid⟩
  | cons action rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at noChanges
    obtain ⟨head, tail⟩ := noChanges
    cases action with
    | assign kind slot expr =>
      let next := { snapshot with values := setValue kind slot (eval snapshot fields expr) snapshot.values }
      have nextValid : invariantsHold model next = true :=
        invariant_after_unrelated_set model snapshot slot kind (eval snapshot fields expr) head valid
      exact ih next out tail nextValid
    | emit name expressions =>
      let message : Message := { name := name, fields := expressions.map fun e =>
        { slot := e.slot, kind := e.kind, value := eval snapshot fields e.expression } }
      exact ih snapshot (out ++ [message]) tail valid
    | arm _ _ | cancel _ =>
      contradiction

theorem external_rule_keeps_invariants (model : Model) (rule : Rule)
    (loop : rule.target = rule.source)
    (noChanges : rule.actions.all (keepsInvariants model) = true) :
    FiringPreserves model rule none := by
  intro snapshot fields valid source _
  obtain ⟨after, emitted, executed, sameState, afterValid⟩ :=
    work_keeps_invariants model rule.actions snapshot fields [] noChanges valid
  let transition : Transition :=
    { after := { after with state := rule.target }
      rule := rule.id
      event := rule.event
      fields := fields
      emitted := emitted }
  refine ⟨transition, ?_, ?_⟩
  · unfold candidate
    simp only [withoutFiring, executed, transition]
  · change invariantsHold model { after with state := rule.target } = true
    rw [loop, ← source, ← sameState]
    exact afterValid

end FormalSpecAgent.InvariantFootprint
