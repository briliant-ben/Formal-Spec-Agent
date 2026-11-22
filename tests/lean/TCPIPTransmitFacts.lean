import Approved
import OctetFacts
import SequenceFacts
namespace TCPIPTransmitFacts
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts

theorem both (s : Snapshot) (f : Values) (x y : Expr .boolean)
    (enabled : TypedMachine.eval s f (.boolAnd x y) = true) :
    TypedMachine.eval s f x = true ∧ TypedMachine.eval s f y = true := by
  change (TypedMachine.eval s f x && TypedMachine.eval s f y) = true at enabled
  simpa only [Bool.and_eq_true] using enabled

def transmitGuard (first : Bool) : Expr .boolean := if first then e1227 else e1245

theorem guardFacts (s : Snapshot) (f : Values) (first : Bool)
    (guard : TypedMachine.eval s f (transmitGuard first) = true) :
    TypedMachine.eval s f e923 = true ∧ 1 ≤ TypedMachine.eval s f e925 ∧
    1 ≤ TypedMachine.eval s f e1222 := by
  have capacity : TypedMachine.eval s f e1225 = true := by
    cases first
    · exact (both s f e1225 e1243 (both s f e923 e1244 guard).2).1
    · exact (both s f e1225 e930 (both s f e923 e1226 guard).2).1
  have established : TypedMachine.eval s f e923 = true := by
    cases first
    · exact (both s f e923 e1244 guard).1
    · exact (both s f e923 e1226 guard).1
  obtain ⟨buffer, window⟩ := both s f e1220 e1223 (both s f e3 e1224 capacity).2
  exact ⟨established, of_decide_eq_true (both s f e3 e1219 buffer).2, of_decide_eq_true window⟩

theorem continuing_flight (s : Snapshot) (f : Values)
    (enabled : TypedMachine.eval s f (transmitGuard false) = true) :
    TypedMachine.eval s f e1243 = true :=
  (both s f e1225 e1243 (both s f e923 e1244 enabled).2).2

abbrev sendCount (s : Snapshot) (f : Values) := TypedMachine.eval s f e1230

theorem countFacts (s : Snapshot) (f : Values)
    (hasBytes : 1 ≤ TypedMachine.eval s f e925)
    (space : 1 ≤ TypedMachine.eval s f e1222) :
    1 ≤ sendCount s f ∧ sendCount s f ≤ TypedMachine.eval s f e925 ∧
    sendCount s f ≤ TypedMachine.eval s f e1222 ∧ sendCount s f ≤ 4 := by
  change 1 ≤ min 4 (min (TypedMachine.eval s f e925) (TypedMachine.eval s f e1222)) ∧ _
  have minimum : 1 ≤ min (TypedMachine.eval s f e925) (TypedMachine.eval s f e1222) :=
    Int.le_min.mpr ⟨hasBytes, space⟩
  exact ⟨Int.le_min.mpr ⟨by decide, minimum⟩,
    Int.le_trans (Int.min_le_right ..) (Int.min_le_left ..),
    Int.le_trans (Int.min_le_right ..) (Int.min_le_right ..), Int.min_le_left ..⟩

abbrev pendingBytes (s : Snapshot) (f : Values) := TypedMachine.eval s f e924
abbrev unacked (s : Snapshot) (f : Values) := TypedMachine.eval s f e928
abbrev sendPrefix (s : Snapshot) (f : Values) := byteSlice (pendingBytes s f) 0 (sendCount s f)
abbrev sendSuffix (s : Snapshot) (f : Values) :=
  byteSlice (pendingBytes s f) (sendCount s f) (pendingBytes s f).length
abbrev afterFlight (s : Snapshot) (f : Values) := unacked s f ++ sendPrefix s f

theorem data_preserves (s : Snapshot) (f : Values)
    (inv : invariantsHold model s = true) (established : TypedMachine.eval s f e923 = true)
    (hasBytes : 1 ≤ TypedMachine.eval s f e925) (space : 1 ≤ TypedMachine.eval s f e1222) :
    ((sendSuffix s f).length : Int) + (afterFlight s f).length ≤ 16 ∧
    ((afterFlight s f).length : Int) ≤ TypedMachine.eval s f e1221 ∧
    1 ≤ ((afterFlight s f).length : Int) ∧
    ValueOps.seqAdd (TypedMachine.eval s f e763) (sendCount s f) =
      ValueOps.seqAdd (TypedMachine.eval s f e976) (afterFlight s f).length := by
  obtain ⟨positive, prepared, window, _⟩ := countFacts s f hasBytes space
  have nonneg : 0 ≤ sendCount s f := Int.le_trans (by decide : (0 : Int) ≤ 1) positive
  have prefixLen : ((sendPrefix s f).length : Int) = sendCount s f :=
    OctetFacts.prefix_length _ _ nonneg prepared
  have suffixLen : ((sendSuffix s f).length : Int) = (pendingBytes s f).length - sendCount s f :=
    OctetFacts.suffix_length _ _ nonneg prepared
  have flightLen : ((afterFlight s f).length : Int) = (unacked s f).length + sendCount s f := by
    rw [List.length_append]
    change (↑(unacked s f).length : Int) + ↑(sendPrefix s f).length = _
    rw [prefixLen]
  have old := List.all_eq_true.mp inv e1690 (by rw [model_invariants]; simp)
  have phase : TypedMachine.eval s zeroValues e923 = true := established
  change (!TypedMachine.eval s zeroValues e923 || TypedMachine.eval s zeroValues e1689) = true at old
  simp only [phase, Bool.not_true, Bool.false_or] at old
  have sequence : TypedMachine.eval s f e763 =
      ValueOps.seqAdd (TypedMachine.eval s f e976) (unacked s f).length := of_decide_eq_true old
  have room := List.all_eq_true.mp inv e1691 (by rw [model_invariants]; simp)
  have capacity : ((pendingBytes s f).length : Int) + (unacked s f).length ≤ 16 :=
    of_decide_eq_true room
  change sendCount s f ≤ TypedMachine.eval s f e1221 - (unacked s f).length at window
  rw [flightLen, suffixLen]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have combine (a b n : Int) (h : a + b ≤ 16) : a - n + (b + n) ≤ 16 := by omega
    exact combine _ _ _ capacity
  · have fit (n old available : Int) (h : n ≤ available - old) : old + n ≤ available := by omega
    exact fit _ _ _ window
  · have enough (n : Int) (old : Nat) (h : 1 ≤ n) : 1 ≤ (old : Int) + n := by omega
    exact enough _ _ positive
  · rw [← SequenceFacts.add_add, ← sequence]

end TCPIPTransmitFacts
