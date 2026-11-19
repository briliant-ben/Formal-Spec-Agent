import Approved
import GuardDiscriminators

namespace TCPIPFrameCatalog
open Approved FormalSpecAgent.TypedMachine
open FormalSpecAgent.GuardDiscriminators FormalSpecAgent.TimedObligations

def block (index : Nat) : List Rule :=
  (conflictGroup_4.drop (index * 30)).take 30

def pairId (pair : Rule × Rule) : Nat × Nat := (pair.1.id, pair.2.id)

def blockIds (index : Nat) : List (Nat × Nat) :=
  (residualPairsFrom (block index) conflictGroup_4).map pairId

set_option maxRecDepth 16384 in
theorem exact_partition : block 0 ++ block 1 ++ block 2 ++ block 3 ++ block 4 ++ block 5 ++ block 6 ++ block 7 =
    conflictGroup_4 := by
  rfl

set_option maxRecDepth 16384 in
theorem merge_blocks : (residualPairs conflictGroup_4).map pairId =
    blockIds 0 ++ blockIds 1 ++ blockIds 2 ++ blockIds 3 ++
      blockIds 4 ++ blockIds 5 ++ blockIds 6 ++ blockIds 7 := by
  unfold residualPairs
  have partition := congrArg
    (fun rules : List Rule => (residualPairsFrom rules conflictGroup_4).map pairId)
    exact_partition
  rw [← partition]
  simp only [residualPairsFrom_append, List.map_append, blockIds]

private theorem member_rules {rules : List Rule} {p : Rule × Rule}
    (member : p ∈ residualPairs rules) : p.1 ∈ rules ∧ p.2 ∈ rules := by
  obtain ⟨a, ha, hm⟩ := List.mem_flatMap.mp member
  obtain ⟨b, hb, same⟩ := List.mem_map.mp hm
  obtain ⟨r, hr, equal⟩ := List.mem_map.mp (List.mem_filter.mp hb).1
  rw [← same, ← equal]
  exact ⟨ha, hr⟩

private theorem rule_identity {rules : List Rule} (unique : (rules.map Rule.id).Nodup)
    {a b : Rule} (ha : a ∈ rules) (hb : b ∈ rules) (same : a.id = b.id) : a = b := by
  induction rules with
  | nil => simp at ha
  | cons r rs ih =>
    have parts := List.nodup_cons.mp unique
    rcases List.mem_cons.mp ha with eqA | memA <;> rcases List.mem_cons.mp hb with eqB | memB
    · exact eqA.trans eqB.symm
    · exact False.elim (parts.1 (List.mem_map.mpr ⟨b, memB, same.symm.trans (congrArg Rule.id eqA)⟩))
    · exact False.elim (parts.1 (List.mem_map.mpr ⟨a, memA, same.trans (congrArg Rule.id eqB)⟩))
    · exact ih parts.2 memA memB

theorem conflict_of_catalog (model : Model) (rules : List Rule) (known : List (Rule × Rule))
    (unique : (rules.map Rule.id).Nodup)
    (catalog : (residualPairs rules).map pairId = known.map pairId)
    (knownRules : ∀ p ∈ known, p.1 ∈ rules ∧ p.2 ∈ rules)
    (verified : Each (PairDisjoint model) known) : ConflictFree model rules := by
  apply conflict_from_residual
  generalize h : residualPairs rules = pairs
  suffices ∀ p ∈ pairs, PairDisjoint model p by
    clear h catalog
    induction pairs with
    | nil => trivial
    | cons p rest ih =>
      exact ⟨this p (by simp), ih (fun q member => this q (List.mem_cons_of_mem _ member))⟩
  intro p member
  have pMembers := member_rules (h ▸ member)
  have key : pairId p ∈ known.map pairId := by
    rw [← catalog]
    exact List.mem_map.mpr ⟨p, h ▸ member, rfl⟩
  obtain ⟨q, hq, keys⟩ := List.mem_map.mp key
  have qMembers := knownRules q hq
  have left := rule_identity unique qMembers.1 pMembers.1 (congrArg Prod.fst keys)
  have right := rule_identity unique qMembers.2 pMembers.2 (congrArg Prod.snd keys)
  have equal : q = p := Prod.ext left right
  exact equal ▸ verified.of_mem hq

end TCPIPFrameCatalog
