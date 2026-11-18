import TimedObligations

namespace FormalSpecAgent.GuardDiscriminators

open TypedIR

inductive InputSlot where
  | variable : Nat → InputSlot
  | field : Nat → InputSlot
  deriving DecidableEq

def InputSlot.read (slot : InputSlot) (kind : Kind) (ctx : Context) : Value kind :=
  match slot with
  | .variable index => getValue kind ctx.store index
  | .field index => getValue kind ctx.fields index

inductive Fact where
  | integer : InputSlot → Int → Fact
  | text : InputSlot → String → Fact
  | boolean : InputSlot → Bool → Fact

def Fact.holds (ctx : Context) : Fact → Prop
  | .integer slot value => slot.read .integer ctx = value
  | .text slot value => slot.read .text ctx = value
  | .boolean slot value => slot.read .boolean ctx = value

def facts {kind : Kind} (guard : Expr kind) : List Fact :=
  match guard with
  | .boolAnd left right => facts left ++ facts right
  | .equal .integer (.variable _ slot) (.literal _ value) => [.integer (.variable slot) value]
  | .equal .integer (.field _ slot) (.literal _ value) => [.integer (.field slot) value]
  | .equal .text (.variable _ slot) (.literal _ value) => [.text (.variable slot) value]
  | .equal .text (.field _ slot) (.literal _ value) => [.text (.field slot) value]
  | .equal .boolean (.variable _ slot) (.literal _ value) => [.boolean (.variable slot) value]
  | .equal .boolean (.field _ slot) (.literal _ value) => [.boolean (.field slot) value]
  | _ => []
termination_by structural guard

private def Enabled {kind : Kind} (guard : Expr kind) (ctx : Context) : Prop :=
  match kind, guard with
  | .boolean, guard => TypedIR.eval guard ctx = true
  | _, _ => True

private theorem facts_sound {kind : Kind} (guard : Expr kind) (ctx : Context)
    (enabled : Enabled guard ctx) (fact : Fact) (member : fact ∈ facts guard) :
    fact.holds ctx := by
  fun_induction facts guard with
  | case1 left right ihLeft ihRight =>
    simp only [Enabled, TypedIR.eval, Bool.and_eq_true] at enabled
    rcases List.mem_append.mp member with inLeft | inRight
    · exact ihLeft enabled.1 inLeft
    · exact ihRight enabled.2 inRight
  | _ =>
    simp_all [Enabled, TypedIR.eval, equalValue, Fact.holds, InputSlot.read] <;>
      exact of_decide_eq_true enabled

def Fact.clash : Fact → Fact → Bool
  | .integer x a, .integer y b => decide (x = y ∧ a ≠ b)
  | .text x a, .text y b => decide (x = y ∧ a ≠ b)
  | .boolean x a, .boolean y b => decide (x = y ∧ a ≠ b)
  | _, _ => false

theorem Fact.clash_sound (left right : Fact) (ctx : Context)
    (clash : left.clash right = true) (a : left.holds ctx) (b : right.holds ctx) : False := by
  cases left <;> cases right <;> simp only [Fact.clash, decide_eq_true_eq] at clash
  all_goals
    first
    | contradiction
    | obtain ⟨rfl, different⟩ := clash
      exact different (a.symm.trans b)

def separated (left right : List Fact) : Bool :=
  left.any fun a => right.any fun b => a.clash b

theorem separated_sound (left right : Expr .boolean) (ctx : Context)
    (check : separated (facts left) (facts right) = true) :
    TypedIR.eval left ctx = false ∨ TypedIR.eval right ctx = false := by
  obtain ⟨a, ha, other⟩ := List.any_eq_true.mp check
  obtain ⟨b, hb, clash⟩ := List.any_eq_true.mp other
  cases leftValue : TypedIR.eval left ctx
  · exact Or.inl rfl
  cases rightValue : TypedIR.eval right ctx
  · exact Or.inr rfl
  exact False.elim (Fact.clash_sound a b ctx clash
    (facts_sound left ctx leftValue a ha) (facts_sound right ctx rightValue b hb))

open TypedMachine TimedObligations

/-- Pairs still requiring semantic proofs. Facts are collected once per rule.
A pair is omitted only when a sound check proves the guards cannot both hold. -/
def residualPairs (rules : List Rule) : List (Rule × Rule) :=
  let annotated := rules.map fun r => (r, facts r.guard)
  annotated.flatMap fun a =>
    (annotated.filter fun b => a.1.id < b.1.id && !separated a.2 b.2).map
      fun b => (a.1, b.1)

def PairDisjoint (model : Model) (pair : Rule × Rule) : Prop :=
  ∀ (s : Snapshot) (f : Values), invariantsHold model s = true →
    (pair.1.source = s.state ∨ pair.2.source = s.state) →
    eval s f pair.1.guard = false ∨ eval s f pair.2.guard = false

theorem conflict_from_residual (model : Model) (rules : List Rule)
    (remaining : Each (PairDisjoint model) (residualPairs rules)) :
    ConflictFree model rules := by
  intro s f valid left hl right hr distinct source
  have check (a b : Rule) (ha : a ∈ rules) (hb : b ∈ rules) (ordered : a.id < b.id)
      (atSource : a.source = s.state ∨ b.source = s.state) :
      eval s f a.guard = false ∨ eval s f b.guard = false := by
    cases result : separated (facts a.guard) (facts b.guard)
    · have member : (a, b) ∈ residualPairs rules := by
        apply List.mem_flatMap.mpr
        refine ⟨(a, facts a.guard), List.mem_map.mpr ⟨a, ha, rfl⟩, ?_⟩
        apply List.mem_map.mpr
        refine ⟨(b, facts b.guard), List.mem_filter.mpr ⟨List.mem_map.mpr ⟨b, hb, rfl⟩, ?_⟩, rfl⟩
        simp [ordered, result]
      exact remaining.of_mem member s f valid atSource
    · exact separated_sound a.guard b.guard (context s f) result
  rcases Nat.lt_or_gt_of_ne distinct with ordered | ordered
  · exact check left right hl hr ordered (Or.inl source)
  · exact Or.symm (check right left hr hl ordered (Or.inr source))

theorem conflict_from_empty (model : Model) (rules : List Rule)
    (empty : residualPairs rules = []) : ConflictFree model rules := by
  apply conflict_from_residual
  rw [empty]
  trivial

end FormalSpecAgent.GuardDiscriminators
