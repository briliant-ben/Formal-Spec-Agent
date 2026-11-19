import ValueOps
namespace FormalSpecAgent.SequenceFacts

open ValueOps

private theorem add_value (base : Seq32) (n : Int) :
    ((seqAdd base n).val : Int) = ((base.val : Int) + n) % 4294967296 := by
  have nonnegative := Int.emod_nonneg ((base.val : Int) + n) (by decide : (4294967296 : Int) ≠ 0)
  have bounded := Int.emod_lt_of_pos ((base.val : Int) + n) (by decide : (0 : Int) < 4294967296)
  change (((((base.val : Int) + n) % 4294967296).toNat % 4294967296 : Nat) : Int) =
    ((base.val : Int) + n) % 4294967296
  rw [Nat.mod_eq_of_lt (by omega)]
  exact Int.toNat_of_nonneg nonnegative

theorem add_distance (base ack : Seq32) : seqAdd base (seqDistance base ack) = ack := by
  apply Fin.ext
  have valEq := add_value base (seqDistance base ack)
  have limit := ack.isLt
  unfold seqDistance at valEq
  calc
    (seqAdd base (((ack.val : Int) - (base.val : Int)) % 4294967296)).val
        = ((((base.val : Int) + (((ack.val : Int) - (base.val : Int)) % 4294967296)) %
              4294967296).toNat) := by omega
    _ = ack.val := by
      rw [Int.add_emod_emod]
      have cancel : (base.val : Int) + ((ack.val : Int) - (base.val : Int)) = ack.val := by omega
      rw [cancel, Int.emod_eq_of_lt (by omega) (by omega)]
      simp

theorem add_add (base : Seq32) (a b : Int) : seqAdd (seqAdd base a) b = seqAdd base (a+b) := by
  apply Fin.ext
  have l := add_value (seqAdd base a) b
  have h := add_value base a
  have r := add_value base (a+b)
  rw [h, Int.emod_add_emod, Int.add_assoc] at l
  omega

end FormalSpecAgent.SequenceFacts
