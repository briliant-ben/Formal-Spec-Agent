import Foundation

namespace FormalSpecAgent.OctetFacts

theorem prefix_length (data : Bytes) (n : Int) (lo : 0 ≤ n) (hi : n ≤ (data.length : Int)) :
    (Int.ofNat (byteSlice data 0 n).length) = n := by
  have available : n.toNat ≤ data.length := by omega
  simp [byteSlice, List.length_take, Nat.min_eq_left available, Int.toNat_of_nonneg lo]

theorem suffix_length (data : Bytes) (n : Int) (lo : 0 ≤ n) (hi : n ≤ (data.length : Int)) :
    ((byteSlice data n data.length).length : Int) = (data.length : Int) - n := by
  unfold byteSlice
  rw [List.length_take, List.length_drop]
  simp only [Int.toNat_natCast]
  have less : data.length - n.toNat ≤ data.length := Nat.sub_le ..
  rw [Nat.min_eq_right less]
  omega

end FormalSpecAgent.OctetFacts
