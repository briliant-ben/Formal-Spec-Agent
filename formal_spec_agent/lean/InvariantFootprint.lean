import TimedObligations

namespace FormalSpecAgent.InvariantFootprint

open TypedIR TypedMachine TypedContracts TypedFiringContracts TimedObligations

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

private def requiresText {kind : Kind} (guard : Expr kind) (slot : Nat) (value : String) : Bool :=
  match guard with
  | .boolAnd l r => requiresText l slot value || requiresText r slot value
  | .equal .text (.variable .text index) (.literal .text expected) =>
      index == slot && decide (expected = value)
  | _ => false
termination_by structural guard

private def Enabled {kind : Kind} (guard : Expr kind) (ctx : Context) : Prop :=
  match kind with
  | .boolean => TypedIR.eval guard ctx = true
  | _ => False

private theorem requiresText_sound {kind : Kind} (guard : Expr kind) (ctx : Context) (slot : Nat)
    (value : String) (enabled : Enabled guard ctx)
    (found : requiresText guard slot value = true) :
    getValue .text ctx.store slot = value := by
  fun_induction requiresText guard slot value with
  | case1 l r ihL ihR =>
    simp only [Bool.or_eq_true] at found
    change (TypedIR.eval l ctx && TypedIR.eval r ctx) = true at enabled
    simp only [Bool.and_eq_true] at enabled
    exact found.elim (ihL enabled.1) (ihR enabled.2)
  | case2 index expected =>
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at found
    obtain ⟨rfl, rfl⟩ := found
    exact of_decide_eq_true enabled
  | _ => contradiction

private theorem set_current_value (kind : Kind) (slot : Nat) (s : Values) :
    setValue kind slot (getValue kind s slot) s = s := by
  cases s
  cases kind <;> simp only [setValue, getValue, Values.mk.injEq]
  all_goals
    simp only [and_true, true_and]
    funext index
    split
    · subst index
      rfl
    · rfl

private def preservesInputs (model : Model) (before after : Values) : Prop :=
  ∀ (kind : Kind) (slot : Nat), model.invariants.all (ignoresSlot slot) = false →
    getValue kind after slot = getValue kind before slot

private theorem preserves_unrelated (model : Model) (values : Values) (kind : Kind) (slot : Nat)
    (value : Value kind) (unrelated : model.invariants.all (ignoresSlot slot) = true) :
    preservesInputs model values (setValue kind slot value values) := by
  intro readKind readSlot watched
  apply getValue_after_unrelated_set
  intro same
  subst readSlot
  rw [unrelated] at watched
  contradiction

private def guardedNoop (guard : Expr .boolean) : Action → Bool
  | .assign .text slot (.literal .text value) => requiresText guard slot value
  | _ => false

private theorem guarded_noop_assign (model : Model) (original snapshot : Snapshot) (fields : Values)
    (guard : Expr .boolean) (kind : Kind) (slot : Nat) (expr : Expr kind)
    (enabled : TypedMachine.eval original fields guard = true)
    (watched : model.invariants.all (ignoresSlot slot) = false)
    (same : preservesInputs model original.values snapshot.values)
    (accepted : guardedNoop guard (.assign kind slot expr) = true) :
    setValue kind slot (TypedMachine.eval snapshot fields expr) snapshot.values = snapshot.values := by
  cases kind <;> cases expr <;> simp only [guardedNoop] at accepted <;> try contradiction
  rename_i value
  have asserted := requiresText_sound guard (context original fields) slot value enabled accepted
  have current := (same .text slot watched).trans asserted
  change setValue .text slot value snapshot.values = snapshot.values
  rw [← current]
  exact set_current_value .text slot snapshot.values

/-- Keep existing checked effects and literal assignments that are forced to
write their existing value. Only invariant-related slots require a guard fact. -/
def guardedEffect (model : Model) (guard : Expr .boolean) (action : Action) : Bool :=
  keepsInvariants model action || guardedNoop guard action

private theorem work_guarded (model : Model) (actions : List Action) (original snapshot : Snapshot)
    (fields : Values) (out : List Message) (guard : Expr .boolean)
    (enabled : TypedMachine.eval original fields guard = true)
    (safe : actions.all (guardedEffect model guard) = true)
    (same : preservesInputs model original.values snapshot.values)
    (valid : invariantsHold model snapshot = true) :
    ∃ after emitted, work actions snapshot fields out = .ok (after, emitted) ∧
      after.state = snapshot.state ∧ invariantsHold model after = true := by
  induction actions generalizing snapshot out with
  | nil => exact ⟨snapshot, out, rfl, rfl, valid⟩
  | cons action rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at safe
    obtain ⟨head, tail⟩ := safe
    cases action with
    | assign kind slot expr =>
      let value := TypedMachine.eval snapshot fields expr
      let next := { snapshot with values := setValue kind slot value snapshot.values }
      cases related : model.invariants.all (ignoresSlot slot) with
      | true =>
        have legal := invariant_after_unrelated_set model snapshot slot kind value related valid
        have update := preserves_unrelated model snapshot.values kind slot value related
        exact ih next out tail
          (fun readKind readSlot observed => (update readKind readSlot observed).trans
            (same readKind readSlot observed)) legal
      | false =>
        have noop : guardedNoop guard (.assign kind slot expr) = true := by
          simpa only [guardedEffect, keepsInvariants, related, Bool.false_or] using head
        have unchanged := guarded_noop_assign model original snapshot fields guard kind slot expr
          enabled related same noop
        have nextEq : next = snapshot := by
          change { snapshot with values := setValue kind slot value snapshot.values } = snapshot
          rw [unchanged]
        rw [show work (.assign kind slot expr :: rest) snapshot fields out = work rest next fields out from rfl,
          nextEq]
        exact ih snapshot out tail same valid
    | emit name expressions =>
      let message : Message := { name := name, fields := expressions.map fun e =>
        { slot := e.slot, kind := e.kind, value := TypedMachine.eval snapshot fields e.expression } }
      exact ih snapshot (out ++ [message]) tail same valid
    | arm _ _ | cancel _ =>
      contradiction

private theorem guarded_of_unchanged (model : Model) (guard : Expr .boolean) (actions : List Action)
    (noChanges : actions.all (keepsInvariants model) = true) :
    actions.all (guardedEffect model guard) = true := by
  apply List.all_eq_true.mpr
  intro action member
  have unchanged := List.all_eq_true.mp noChanges action member
  simp only [guardedEffect, unchanged, Bool.true_or]

theorem work_keeps_invariants (model : Model) (actions : List Action) (snapshot : Snapshot)
    (fields : Values) (out : List Message)
    (noChanges : actions.all (keepsInvariants model) = true)
    (valid : invariantsHold model snapshot = true) :
    ∃ after emitted, work actions snapshot fields out = .ok (after, emitted) ∧
      after.state = snapshot.state ∧ invariantsHold model after = true := by
  exact work_guarded model actions snapshot snapshot fields out (.literal .boolean true) rfl
    (guarded_of_unchanged model _ actions noChanges) (fun _ _ _ => rfl) valid

theorem external_rule_guarded_invariants (model : Model) (rule : Rule)
    (loop : rule.target = rule.source)
    (safe : rule.actions.all (guardedEffect model rule.guard) = true) :
    FiringPreserves model rule none := by
  intro snapshot fields valid source enabled
  obtain ⟨after, emitted, executed, sameState, afterValid⟩ :=
    work_guarded model rule.actions snapshot snapshot fields [] rule.guard enabled safe
      (fun _ _ _ => rfl) valid
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

theorem external_rule_keeps_invariants (model : Model) (rule : Rule)
    (loop : rule.target = rule.source)
    (noChanges : rule.actions.all (keepsInvariants model) = true) :
    FiringPreserves model rule none := by
  exact external_rule_guarded_invariants model rule loop
    (guarded_of_unchanged model rule.guard rule.actions noChanges)

private def acceptsRaw (model : Model) (pair : Rule × Option Nat) : Bool :=
  pair.2.isNone && (pair.1.target == pair.1.source) &&
    pair.1.actions.all (guardedEffect model pair.1.guard)

/-- Raw obligations justified by unchanged invariant inputs, with the exact trigger retained. -/
def guardedRawChecks (model : Model) (ids : List Nat) : List (Rule × Option Nat) :=
  (rawChecks model ids).filter (acceptsRaw model)

theorem guardedRawChecks_sound (model : Model) (ids : List Nat) :
    Each (fun p => FiringPreserves model p.1 p.2) (guardedRawChecks model ids) := by
  generalize exactChecks : guardedRawChecks model ids = checks
  suffices ∀ p ∈ checks, FiringPreserves model p.1 p.2 by
    clear exactChecks
    induction checks with
    | nil => trivial
    | cons pair rest ih =>
      exact ⟨this pair (by simp), ih (fun q h => this q (List.mem_cons_of_mem _ h))⟩
  intro ⟨rule, trigger⟩ member
  have accepted := (List.mem_filter.mp (exactChecks ▸ member)).2
  cases trigger with
  | none =>
    simp only [acceptsRaw, Option.isNone, Bool.true_and, Bool.and_eq_true, beq_iff_eq] at accepted
    exact external_rule_guarded_invariants model rule accepted.1 accepted.2
  | some _ => contradiction

end FormalSpecAgent.InvariantFootprint
