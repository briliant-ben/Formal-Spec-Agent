import Approved
import EffectConditions
import OctetBounds

namespace TCPIPSendWire
open Approved FormalSpecAgent TypedMachine TypedIR TimedObligations EffectConditions

inductive LinkPhase where
  | empty | pending | resolved

def linkGuard : LinkPhase → Expr .boolean
  | .empty => e16 | .pending => e35 | .resolved => e38

def linkClauses : LinkPhase → List (Expr .boolean)
  | .empty => [e1594, e1597, e1601, e1604, e1612, e1614, e1615, e1628, e1721]
  | .pending => [e1612, e1614, e1615, e1721]
  | .resolved => []

def affected (tcpClauses : List (Expr .boolean)) : LinkPhase → List (Expr .boolean)
  | .empty => [e1594, e1597, e1601, e1604, e1612, e1614, e1615, e1628] ++
      tcpClauses ++ [e1706, e1721]
  | .pending => [e1612, e1614, e1615] ++ tcpClauses ++ [e1706, e1721]
  | .resolved => tcpClauses ++ [e1706]

theorem partition (phase : LinkPhase) (tcpClauses : List (Expr .boolean)) (inv : Expr .boolean)
    (member : inv ∈ affected tcpClauses phase) :
    inv ∈ tcpClauses ∨ inv ∈ linkClauses phase ∨ inv = e1706 := by
  cases phase <;> simpa only [affected, linkClauses, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, false_or, or_assoc, or_left_comm, or_comm] using member

/-- Checks seen by the IP queue after a TCP packet is placed in it. Callers
bind each expression to the postconditions generated for the original rule. -/
def queueChecks (packet : Expr .octets) (pending : Expr .boolean) : List (Expr .boolean) :=
  let size := Expr.bytesLength packet
  let empty := Expr.equal .integer size e1
  let noneOwner := Expr.equal .text e208 e5
  let ownerCases := Expr.boolOr (.equal .text e208 e181) (.equal .text e208 e208)
  [.intLe size e244,
   .implies (.intGe size e44) pending,
   .boolOr empty (.intGe size e89),
   .boolAnd (.boolOr noneOwner ownerCases) (.equal .boolean noneOwner empty)]

theorem queue_checked (s : Snapshot) (f : Values) (packet : Expr .octets) (pending : Expr .boolean)
    (bound : OctetBounds.certifies (.intLe (.bytesLength packet) e244) = true)
    (minimum : 28 ≤ OctetBounds.lower packet)
    (pendingTrue : TypedMachine.eval s f pending = true) :
    Each (fun expr => holds [expr] s f = true) (queueChecks packet pending) := by
  let size := Int.ofNat (TypedMachine.eval s f packet).length
  have enough : 28 ≤ size :=
    Int.ofNat_le.mpr (Nat.le_trans minimum (OctetBounds.lower_sound packet (context s f)))
  have nonzero : size ≠ 0 := by omega
  have sizeBound := OctetBounds.certifies_sound _ (context s f) bound
  refine ⟨?_, ?_, ?_, ?_, trivial⟩
  · change (TypedIR.eval (.intLe (.bytesLength packet) e244) (context s f) && true) = true
    rw [sizeBound]
    rfl
  · change ((!decide (1 ≤ size) || TypedMachine.eval s f pending) && true) = true
    simp [pendingTrue]
  · change ((decide (size = 0) || decide (28 ≤ size)) && true) = true
    rw [decide_eq_true enough]
    simp
  · change ((true && decide (false = decide (size = 0))) && true) = true
    simp [nonzero]

def queueClauses : List (Expr .boolean) := [e1612, e1614, e1615, e1721]

theorem queue_from_post (s : Snapshot) (f : Values) (post : Expr .boolean → List (Expr .boolean))
    (packet : Expr .octets) (pending : Expr .boolean)
    (align : queueClauses.map post = (queueChecks packet pending).map (fun e => [e]))
    (bound : OctetBounds.certifies (.intLe (.bytesLength packet) e244) = true)
    (minimum : 28 ≤ OctetBounds.lower packet)
    (pendingTrue : TypedMachine.eval s f pending = true) :
    Each (fun inv => holds (post inv) s f = true) queueClauses := by
  have checked := queue_checked s f packet pending bound minimum pendingTrue
  have packetBound : holds (post e1612) s f = true := by
    have aligned := congrArg List.head? align
    have same : post e1612 = [_] := Option.some.inj aligned
    rw [same]
    exact checked.1
  have next := congrArg List.tail align
  have phase : holds (post e1614) s f = true := by
    have same : post e1614 = [_] := Option.some.inj (congrArg List.head? next)
    rw [same]
    exact checked.2.1
  have rest := congrArg List.tail next
  have payload : holds (post e1615) s f = true := by
    have same : post e1615 = [_] := Option.some.inj (congrArg List.head? rest)
    rw [same]
    exact checked.2.2.1
  have owner : holds (post e1721) s f = true := by
    have same : post e1721 = [_] := Option.some.inj (congrArg (fun xs => xs.tail.head?) rest)
    rw [same]
    exact checked.2.2.2.1
  exact ⟨packetBound, phase, payload, owner, trivial⟩

theorem pending_cache_requirements (s : Snapshot) (f : Values)
    (empty : TypedMachine.eval s f e16 = true) (valid : invariantsHold model s = true) :
    TypedMachine.eval s f e1587 = true ∧ TypedMachine.eval s f e1592 = true := by
  have before := List.all_eq_true.mp valid e1594 (by rw [model_invariants]; simp)
  have phase : TypedMachine.eval s zeroValues e16 = true := empty
  change (!TypedMachine.eval s zeroValues e16 ||
    ((TypedMachine.eval s zeroValues e1587 && TypedMachine.eval s zeroValues e1589) &&
      TypedMachine.eval s zeroValues e1592)) = true at before
  simp only [phase, Bool.not_true, Bool.false_or, Bool.and_eq_true] at before
  exact ⟨before.1.1, before.2⟩

end TCPIPSendWire
