import Approved
import GuardDiscriminators

namespace TCPIPFrameCensus

open FormalSpecAgent.TypedMachine FormalSpecAgent.GuardDiscriminators Approved

abbrev Counts := Nat × Nat × Nat × Nat

def countPair (counts : Counts) (pair : Rule × Rule) : Counts :=
  let (link, mixed, tcp, malformed) := counts
  let (left, right) := pair
  let malformed := if left.id == 334 || right.id == 334 then malformed + 1 else malformed
  if left.id < 64 then
    if right.id < 64 then (link + 1, mixed, tcp, malformed)
    else (link, mixed + 1, tcp, malformed)
  else
    (link, mixed, tcp + 1, malformed)

def block (index : Nat) : List Rule :=
  (conflictGroup_4.drop (index * 60)).take 60

def fromBlock (index : Nat) (prior : Counts) : Counts :=
  (residualPairsFrom (block index) conflictGroup_4).foldl countPair prior

set_option maxRecDepth 16384 in
theorem exact_partition : block 0 ++ block 1 ++ block 2 ++ block 3 = conflictGroup_4 := by
  rfl

set_option maxRecDepth 16384 in
theorem merge_blocks :
    (residualPairs conflictGroup_4).foldl countPair (0, 0, 0, 0) =
      fromBlock 3 (fromBlock 2 (fromBlock 1 (fromBlock 0 (0, 0, 0, 0)))) := by
  unfold residualPairs
  have partition := congrArg
    (fun rules : List Rule => (residualPairsFrom rules conflictGroup_4).foldl countPair (0, 0, 0, 0))
    exact_partition
  rw [← partition]
  simp only [residualPairsFrom_append, List.foldl_append, fromBlock]

end TCPIPFrameCensus
