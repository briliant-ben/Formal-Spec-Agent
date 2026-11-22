import Approved
import EffectConditions
import GuardedSuffix

namespace TCPIPEmptyResponses
set_option maxRecDepth 16384
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts
open EffectConditions EffectFootprint GuardedSuffix TimedObligations

private theorem both (s : Snapshot) (f : Values) (x y : Expr .boolean)
    (checked : TypedMachine.eval s f (.boolAnd x y) = true) :
    TypedMachine.eval s f x = true ∧ TypedMachine.eval s f y = true := by
  change (TypedMachine.eval s f x && TypedMachine.eval s f y) = true at checked
  simpa only [Bool.and_eq_true] using checked

private def prefixActions (r : Rule) := r.actions.dropLast
private def cut (r : Rule) : Rule := {r with actions := prefixActions r}

/-- Proofs shared by identical ordered actions and identical machine states.
The actual rule's own guard remains a separate premise. -/
private def Conditions (r : Rule) (s : Snapshot) (f : Values) : Prop :=
  holds (obligationsFor (cut r) none []) s f = true ∧
    ∀ inv ∈ model.invariants, ignoresFiring inv (cut r) none = false →
      holds (obligationsFor (cut r) none [inv]) s f = true

private theorem from_catalog (r : Rule) (s : Snapshot) (f : Values) (affected : List (Expr .boolean))
    (catalog : model.invariants.filter (fun inv => !ignoresFiring inv (cut r) none) = affected)
    (total : holds (obligationsFor (cut r) none []) s f = true)
    (checked : Each (fun inv => holds (obligationsFor (cut r) none [inv]) s f = true) affected) :
    Conditions r s f := by
  refine ⟨total, ?_⟩
  intro inv member seen
  apply checked.of_mem
  rw [← catalog]
  exact List.mem_filter.mpr ⟨member, by simp [seen]⟩

private theorem reuse (r base : Rule) (s : Snapshot) (f : Values)
    (source : r.source = base.source) (target : r.target = base.target)
    (actions : prefixActions r = prefixActions base) (baseChecked : Conditions base s f) :
    Conditions r s f := by
  have obligations (invariants : List (Expr .boolean)) :
      obligationsFor (cut r) none invariants = obligationsFor (cut base) none invariants := by
    simp only [obligationsFor, cut, actions, target]
  have footprint (inv : Expr .boolean) :
      ignoresFiring inv (cut r) none = ignoresFiring inv (cut base) none := by
    simp only [ignoresFiring, cut, actions, source, target]
  refine ⟨(obligations []).symm ▸ baseChecked.1, ?_⟩
  intro inv member seen
  rw [footprint] at seen
  rw [obligations]
  exact baseChecked.2 inv member seen

private theorem response (r : Rule)
    (shape : r.actions = prefixActions r ++ [.assign .text 56 e807])
    (untouched : (prefixActions r).all (ignoresAction (.variable .text 56)) = true)
    (established : ∀ s f, TypedMachine.eval s f r.guard = true → TypedMachine.eval s f e923 = true)
    (checked : ∀ s f, invariantsHold model s = true → TypedMachine.eval s f r.guard = true →
      Conditions r s f) :
    FiringPreserves model r none := by
  have shorter : FiringPreserves model (cut r) none := by
    apply preserves_touched
    intro s f valid _ enabled
    exact checked s f valid enabled
  apply preserves_after_removing_text model r none (prefixActions r) 56
    (TypedMachine.eval initial zeroValues e807) shape untouched
  · intro s f enabled
    exact of_decide_eq_true (established s f enabled)
  · exact shorter

private theorem resolved_conditions (s : Snapshot) (f : Values) : Conditions rule_257 s f := by
  exact from_catalog rule_257 s f [e1706] rfl rfl ⟨rfl, trivial⟩

set_option maxHeartbeats 1600000 in
private theorem pending_conditions (s : Snapshot) (f : Values)
    (pending : TypedMachine.eval s f e35 = true) : Conditions rule_256 s f := by
  refine from_catalog rule_256 s f [e1612, e1614, e1615, e1706, e1721] rfl rfl ?_
  refine ⟨rfl, ?_, rfl, rfl, rfl, trivial⟩
  change (TypedMachine.eval s f e35 && true) = true
  simp [pending]

set_option maxHeartbeats 1600000 in
private theorem empty_conditions (s : Snapshot) (f : Values)
    (valid : invariantsHold model s = true) (empty : TypedMachine.eval s f e16 = true) :
    Conditions rule_255 s f := by
  have prior := List.all_eq_true.mp valid e1594 (by rw [model_invariants]; simp)
  change (!TypedMachine.eval s zeroValues e16 || TypedMachine.eval s zeroValues e1593) = true at prior
  have phase : TypedMachine.eval s zeroValues e16 = true := empty
  simp only [phase, Bool.not_true, Bool.false_or] at prior
  change ((TypedMachine.eval s zeroValues e1587 && TypedMachine.eval s zeroValues e1589) &&
    TypedMachine.eval s zeroValues e1592) = true at prior
  simp only [Bool.and_eq_true] at prior
  have mac : TypedMachine.eval s f e1587 = true := prior.1.1
  have cache : TypedMachine.eval s f e1592 = true := prior.2
  refine from_catalog rule_255 s f [e1594, e1597, e1601, e1604, e1612, e1614, e1615, e1628, e1706, e1721]
    rfl rfl ?_
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
  change (((TypedMachine.eval s f e1587 && true) && TypedMachine.eval s f e1592) && true) = true
  simp [mac, cache]

theorem future_ack_empty : Approved.raw_255_external := by
  apply response rule_255 rfl (by decide +kernel)
  · intro s f enabled
    exact (both s f e923 e1322 (both s f e1323 e721 (both s f e1324 e16 enabled).1).1).1
  · intro s f valid enabled
    exact reuse rule_255 rule_255 s f rfl rfl rfl (empty_conditions s f valid (both s f e1324 e16 enabled).2)

theorem future_ack_pending : Approved.raw_256_external := by
  apply response rule_256 rfl (by decide +kernel)
  · intro s f enabled
    exact (both s f e923 e1322 (both s f e1323 e721 (both s f e1324 e35 enabled).1).1).1
  · intro s f _ enabled
    exact reuse rule_256 rule_256 s f rfl rfl rfl (pending_conditions s f (both s f e1324 e35 enabled).2)

theorem future_ack_resolved : Approved.raw_257_external := by
  apply response rule_257 rfl (by decide +kernel)
  · intro s f enabled
    exact (both s f e923 e1322 (both s f e1323 e721 (both s f e1324 e38 enabled).1).1).1
  · intro s f _ _
    exact reuse rule_257 rule_257 s f rfl rfl rfl (resolved_conditions s f)

theorem duplicate_data_empty : Approved.raw_267_external := by
  apply response rule_267 rfl (by decide +kernel)
  · intro s f enabled
    exact (both s f e923 e1394 (both s f e1395 e721 (both s f e1396 e16 enabled).1).1).1
  · intro s f valid enabled
    exact reuse rule_267 rule_255 s f rfl rfl rfl (empty_conditions s f valid (both s f e1396 e16 enabled).2)

theorem duplicate_data_pending : Approved.raw_268_external := by
  apply response rule_268 rfl (by decide +kernel)
  · intro s f enabled
    exact (both s f e923 e1394 (both s f e1395 e721 (both s f e1396 e35 enabled).1).1).1
  · intro s f _ enabled
    exact reuse rule_268 rule_256 s f rfl rfl rfl (pending_conditions s f (both s f e1396 e35 enabled).2)

theorem duplicate_data_resolved : Approved.raw_269_external := by
  apply response rule_269 rfl (by decide +kernel)
  · intro s f enabled
    exact (both s f e923 e1394 (both s f e1395 e721 (both s f e1396 e38 enabled).1).1).1
  · intro s f _ _
    exact reuse rule_269 rule_257 s f rfl rfl rfl (resolved_conditions s f)

theorem ahead_data_empty : Approved.raw_270_external := by
  apply response rule_270 rfl (by decide +kernel)
  · intro s f enabled
    exact (both s f e923 e1402 (both s f e1403 e721 (both s f e1404 e16 enabled).1).1).1
  · intro s f valid enabled
    exact reuse rule_270 rule_255 s f rfl rfl rfl (empty_conditions s f valid (both s f e1404 e16 enabled).2)

theorem ahead_data_pending : Approved.raw_271_external := by
  apply response rule_271 rfl (by decide +kernel)
  · intro s f enabled
    exact (both s f e923 e1402 (both s f e1403 e721 (both s f e1404 e35 enabled).1).1).1
  · intro s f _ enabled
    exact reuse rule_271 rule_256 s f rfl rfl rfl (pending_conditions s f (both s f e1404 e35 enabled).2)

theorem ahead_data_resolved : Approved.raw_272_external := by
  apply response rule_272 rfl (by decide +kernel)
  · intro s f enabled
    exact (both s f e923 e1402 (both s f e1403 e721 (both s f e1404 e38 enabled).1).1).1
  · intro s f _ _
    exact reuse rule_272 rule_257 s f rfl rfl rfl (resolved_conditions s f)

theorem zero_window_empty : Approved.raw_273_external := by
  apply response rule_273 rfl (by decide +kernel)
  · intro s f enabled
    exact (both s f e923 e1416 (both s f e1417 e721 (both s f e1418 e16 enabled).1).1).1
  · intro s f valid enabled
    exact reuse rule_273 rule_255 s f rfl rfl rfl (empty_conditions s f valid (both s f e1418 e16 enabled).2)

theorem zero_window_pending : Approved.raw_274_external := by
  apply response rule_274 rfl (by decide +kernel)
  · intro s f enabled
    exact (both s f e923 e1416 (both s f e1417 e721 (both s f e1418 e35 enabled).1).1).1
  · intro s f _ enabled
    exact reuse rule_274 rule_256 s f rfl rfl rfl (pending_conditions s f (both s f e1418 e35 enabled).2)

theorem zero_window_resolved : Approved.raw_275_external := by
  apply response rule_275 rfl (by decide +kernel)
  · intro s f enabled
    exact (both s f e923 e1416 (both s f e1417 e721 (both s f e1418 e38 enabled).1).1).1
  · intro s f _ _
    exact reuse rule_275 rule_257 s f rfl rfl rfl (resolved_conditions s f)

def firings : List (Rule × Option Nat) :=
  [(rule_255, none), (rule_256, none), (rule_257, none), (rule_267, none),
   (rule_268, none), (rule_269, none), (rule_270, none), (rule_271, none),
   (rule_272, none), (rule_273, none), (rule_274, none), (rule_275, none)]

theorem checked : Each (fun p => FiringPreserves model p.1 p.2) firings :=
  ⟨future_ack_empty, future_ack_pending, future_ack_resolved, duplicate_data_empty,
   duplicate_data_pending, duplicate_data_resolved, ahead_data_empty, ahead_data_pending,
   ahead_data_resolved, zero_window_empty, zero_window_pending, zero_window_resolved, trivial⟩

private theorem externalMember (index : Nat) (rule : Rule)
    (selected : model.rules[index]? = some rule) (external : rule.event ∈ model.externalEvents) :
    (rule, none) ∈ rawChecks model declaredTimers :=
  raw_external_member model declaredTimers rule (List.mem_iff_getElem?.mpr ⟨index, selected⟩) external

theorem members : Each (fun p => p ∈ rawChecks model declaredTimers) firings :=
  ⟨externalMember 255 rule_255 rfl (by decide),
   externalMember 256 rule_256 rfl (by decide),
   externalMember 257 rule_257 rfl (by decide),
   externalMember 267 rule_267 rfl (by decide),
   externalMember 268 rule_268 rfl (by decide),
   externalMember 269 rule_269 rfl (by decide),
   externalMember 270 rule_270 rfl (by decide),
   externalMember 271 rule_271 rfl (by decide),
   externalMember 272 rule_272 rfl (by decide),
   externalMember 273 rule_273 rfl (by decide),
   externalMember 274 rule_274 rfl (by decide),
   externalMember 275 rule_275 rfl (by decide), trivial⟩

end TCPIPEmptyResponses
