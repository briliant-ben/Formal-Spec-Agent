import Approved
import EffectConditions

namespace TCPIPQueueRelease
open Approved FormalSpecAgent TypedMachine TypedIR TimedObligations EffectConditions

def queueClauses : List (Expr .boolean) := [e1612, e1614, e1615, e1721]

def releaseReads : ExprRewrite.Rewrite := {
  varRead := fun kind slot =>
    match kind with
    | .octets => if slot = 16 then e951 else .variable .octets slot
    | .text => if slot = 57 then e952 else .variable .text slot
    | .integer => .variable .integer slot
    | .sequence => .variable .sequence slot
    | .boolean => .variable .boolean slot
  field := fun kind slot => .literal kind (getValue kind zeroValues slot)
  stateIs := fun id => .literal .boolean (decide (0 = id))
  timerActive := Expr.timerActive
}

private theorem releaseLen (s : Snapshot) (f : Values) :
    TypedMachine.eval s f (.bytesLength e951) =
      (if TypedMachine.eval s f e209 then 0 else TypedMachine.eval s f e200) := by
  change Int.ofNat (if TypedMachine.eval s f e209 then [] else (TypedMachine.eval s f e199)).length = _
  cases TypedMachine.eval s f e209 <;> rfl

private theorem releaseOwner (s : Snapshot) (f : Values) :
    TypedMachine.eval s f e952 =
      (if TypedMachine.eval s f e209 then TypedMachine.eval s f e5 else TypedMachine.eval s f e204) := rfl

theorem release_queue_safe (s : Snapshot) (f : Values) (valid : invariantsHold model s = true) :
    Each (fun inv => TypedMachine.eval s f (ExprRewrite.run releaseReads inv) = true) queueClauses := by
  have bound : TypedMachine.eval s f e1612 = true :=
    List.all_eq_true.mp valid e1612 (by rw [model_invariants]; simp)
  have pending : TypedMachine.eval s f e1614 = true :=
    List.all_eq_true.mp valid e1614 (by rw [model_invariants]; simp)
  have content : TypedMachine.eval s f e1615 = true :=
    List.all_eq_true.mp valid e1615 (by rw [model_invariants]; simp)
  have owner : TypedMachine.eval s f e1721 = true :=
    List.all_eq_true.mp valid e1721 (by rw [model_invariants]; simp)
  let size := TypedMachine.eval s f (.bytesLength e951)
  let current := TypedMachine.eval s f e952
  have sizeEq := releaseLen s f
  have ownerEq := releaseOwner s f
  refine ⟨?_, ?_, ?_, ?_, trivial⟩
  · change decide (size ≤ 1500) = true
    change size = _ at sizeEq
    rw [sizeEq]
    cases h : TypedMachine.eval s f e209
    · exact bound
    · rfl
  · change (!decide (1 ≤ size) || TypedMachine.eval s f e35) = true
    change size = _ at sizeEq
    rw [sizeEq]
    cases h : TypedMachine.eval s f e209
    · exact pending
    · rfl
  · change (decide (size = 0) || decide (28 ≤ size)) = true
    change size = _ at sizeEq
    rw [sizeEq]
    cases h : TypedMachine.eval s f e209
    · exact content
    · rfl
  · let none := TypedMachine.eval s f e5
    let udp := TypedMachine.eval s f e181
    let tcp := TypedMachine.eval s f e208
    change ((decide (current = none) || (decide (current = udp) || decide (current = tcp))) &&
      decide (decide (current = none) = decide (size = 0))) = true
    change size = _ at sizeEq
    change current = _ at ownerEq
    rw [sizeEq, ownerEq]
    cases h : TypedMachine.eval s f e209
    · exact owner
    · rfl

end TCPIPQueueRelease
