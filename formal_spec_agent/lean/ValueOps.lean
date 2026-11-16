import Foundation

/- Pure IR arithmetic. No buffer truncation, fixed folding fuel or UDP policy.
   Fin witnesses and the recursive folding decrease are checked by the kernel. -/
namespace FormalSpecAgent.ValueOps

abbrev Seq32 := Fin 4294967296

def byteMod (n : Int) : Byte :=
  ⟨(n % 256).toNat % 256, Nat.mod_lt _ (by decide)⟩

def pack8 (n : Int) : Bytes := [byteMod n]
def pack16 (n : Int) : Bytes := [byteMod (n / 256), byteMod n]
def pack32 (n : Int) : Bytes :=
  [byteMod (n / 16777216), byteMod (n / 65536), byteMod (n / 256), byteMod n]

def wordSum (data : Bytes) : Nat :=
  let rec go (acc : Nat) : Bytes → Nat
    | [] => acc
    | [b] => acc + b.val * 256
    | b1 :: b2 :: rest => go (acc + b1.val * 256 + b2.val) rest
  go 0 data

def fold16 (n : Nat) : Nat :=
  if n < 65536 then n else fold16 (n % 65536 + n / 65536)
termination_by n
decreasing_by omega

theorem fold16_bound (n : Nat) : fold16 n < 65536 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [fold16]
    split
    · assumption
    · apply ih
      omega

def checksum (data : Bytes) : Int :=
  65535 - (fold16 (wordSum data) : Int)

theorem checksum_range (data : Bytes) : 0 ≤ checksum data ∧ checksum data ≤ 65535 := by
  have h := fold16_bound (wordSum data)
  unfold checksum
  omega

def seqAdd (s : Seq32) (offset : Int) : Seq32 :=
  ⟨(((s.val : Int) + offset) % 4294967296).toNat % 4294967296,
   Nat.mod_lt _ (by decide)⟩

def seqDistance (a b : Seq32) : Int :=
  ((b.val : Int) - (a.val : Int)) % 4294967296

def seqComparable (a b : Seq32) : Bool := decide (seqDistance a b ≠ 2147483648)
def seqLt (a b : Seq32) : Bool := decide (0 < seqDistance a b ∧ seqDistance a b < 2147483648)
def seqLe (a b : Seq32) : Bool := decide (seqDistance a b < 2147483648)

end FormalSpecAgent.ValueOps
