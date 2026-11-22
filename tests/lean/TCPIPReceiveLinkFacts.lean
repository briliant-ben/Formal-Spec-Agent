import TCPIPReceiveBounds

namespace TCPIPReceiveData
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts
open EffectConditions EffectFootprint GuardedSuffix TimedObligations
set_option maxRecDepth 16384

set_option maxHeartbeats 1000000 in
theorem packet_bound (s : Snapshot) (f : Values) (overlap : Bool) (phase : LinkPhase) :
    checkedClause (rule overlap phase) e1706 s f := by
  cases overlap <;> cases phase <;> rfl

def affected : LinkPhase → List (Expr .boolean)
  | .empty => [e1594, e1597, e1601, e1604, e1612, e1614, e1615, e1628,
               e1692, e1698, e1699, e1706, e1721]
  | .pending => [e1612, e1614, e1615, e1692, e1698, e1699, e1706, e1721]
  | .resolved => [e1692, e1698, e1699, e1706]

theorem empty_cache (s : Snapshot) (f : Values) (overlap : Bool)
    (initiallyEmpty : TypedMachine.eval s f e16 = true)
    (valid : invariantsHold model s = true) :
    checkedClause (rule overlap .empty) e1597 s f := by
  have before := List.all_eq_true.mp valid e1594 (by rw [model_invariants]; simp)
  have empty : TypedMachine.eval s zeroValues e16 = true := initiallyEmpty
  change (!TypedMachine.eval s zeroValues e16 ||
    ((TypedMachine.eval s zeroValues e1587 && TypedMachine.eval s zeroValues e1589) &&
      TypedMachine.eval s zeroValues e1592)) = true at before
  simp only [empty, Bool.not_true, Bool.false_or, Bool.and_eq_true] at before
  have mac : TypedMachine.eval s f e1587 = true := before.1.1
  have noExpiry : TypedMachine.eval s f e1592 = true := before.2
  cases overlap <;>
    change (((TypedMachine.eval s f e1587 && true) && TypedMachine.eval s f e1592) && true) = true <;>
    simp [mac, noExpiry]

set_option maxHeartbeats 900000 in
theorem pending_queue (s : Snapshot) (f : Values) (overlap : Bool)
    (pending : TypedMachine.eval s f e35 = true) :
    checkedClause (rule overlap .pending) e1614 s f := by
  cases overlap <;> change (TypedMachine.eval s f e35 && true) = true <;> simp [pending]

end TCPIPReceiveData
