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

/-- Keys for the supported integer and octet computations. The interpretation
retains slice and out-of-bounds read semantics from TypedIR. -/
inductive Observation where
  | literal : Int → Observation
  | integerSlot : InputSlot → Observation
  | bufferSlot : InputSlot → Observation
  | length : Observation → Observation
  | byteAt : Observation → Observation → Observation
  | slice : Observation → Observation → Observation → Observation
  | add : Observation → Observation → Observation
  | sub : Observation → Observation → Observation
  | mul : Observation → Observation → Observation
  deriving DecidableEq

private def asInt : Int ⊕ Bytes → Int
  | .inl n => n
  | .inr _ => 0

private def asBytes : Int ⊕ Bytes → Bytes
  | .inl _ => []
  | .inr buffer => buffer

def Observation.read (ctx : Context) : Observation → Int ⊕ Bytes
  | .literal value => .inl value
  | .integerSlot loc => .inl (loc.read .integer ctx)
  | .bufferSlot loc => .inr (loc.read .octets ctx)
  | .length buf => .inl (Int.ofNat (asBytes (buf.read ctx)).length)
  | .byteAt buf offset => .inl (FormalSpecAgent.byteAt (asBytes (buf.read ctx)) (asInt (offset.read ctx)))
  | .slice buf offset size =>
    .inr (byteSlice (asBytes (buf.read ctx)) (asInt (offset.read ctx)) (asInt (size.read ctx)))
  | .add l r => .inl (asInt (l.read ctx) + asInt (r.read ctx))
  | .sub l r => .inl (asInt (l.read ctx) - asInt (r.read ctx))
  | .mul l r => .inl (asInt (l.read ctx) * asInt (r.read ctx))

def Observation.integer (ctx : Context) (observation : Observation) : Int :=
  asInt (observation.read ctx)

def observation {kind : Kind} (expr : Expr kind) : Option Observation :=
  match expr with
  | .literal .integer value => some (.literal value)
  | .variable .integer index => some (.integerSlot (.variable index))
  | .field .integer index => some (.integerSlot (.field index))
  | .variable .octets index => some (.bufferSlot (.variable index))
  | .field .octets index => some (.bufferSlot (.field index))
  | .bytesLength buf => (observation buf).map .length
  | .byteAt buf offset => (observation buf).bind fun b => (observation offset).map (.byteAt b)
  | .slice buf offset size => (observation buf).bind fun b => (observation offset).bind fun o =>
      (observation size).map (.slice b o)
  | .add left right => (observation left).bind fun l => (observation right).map (.add l)
  | .sub left right => (observation left).bind fun l => (observation right).map (.sub l)
  | .mul left right => (observation left).bind fun l => (observation right).map (.mul l)
  | _ => none
termination_by structural expr

private def ObservationSound {kind : Kind} (expr : Expr kind) (ctx : Context)
    (obs : Observation) : Prop :=
  match kind, expr with
  | .integer, expr => obs.read ctx = .inl (TypedIR.eval expr ctx)
  | .octets, expr => obs.read ctx = .inr (TypedIR.eval expr ctx)
  | _, _ => False

private theorem observation_sound {kind : Kind} (expr : Expr kind) (ctx : Context)
    (obs : Observation) (found : observation expr = some obs) :
    ObservationSound expr ctx obs := by
  fun_induction observation expr generalizing obs with
  | case6 buf ih =>
    have ⟨b, seen, result⟩ := Option.map_eq_some_iff.mp found
    cases result
    have readBuf : b.read ctx = .inr (TypedIR.eval buf ctx) := ih b seen
    simp only [ObservationSound, Observation.read, TypedIR.eval, readBuf, asBytes]
  | case7 buf offset ihBuf ihOffset =>
    have ⟨b, seenBuf, mapped⟩ := Option.bind_eq_some_iff.mp found
    have ⟨o, seenOffset, result⟩ := Option.map_eq_some_iff.mp mapped
    cases result
    have readBuf : b.read ctx = .inr (TypedIR.eval buf ctx) := ihBuf b seenBuf
    have readOffset : o.read ctx = .inl (TypedIR.eval offset ctx) := ihOffset o seenOffset
    simp only [ObservationSound, Observation.read, TypedIR.eval, readBuf, readOffset, asBytes, asInt]
  | case8 buf offset size ihBuf ihOffset ihSize =>
    have ⟨b, seenBuf, second⟩ := Option.bind_eq_some_iff.mp found
    have ⟨o, seenOffset, mapped⟩ := Option.bind_eq_some_iff.mp second
    have ⟨n, seenSize, result⟩ := Option.map_eq_some_iff.mp mapped
    cases result
    have readBuf : b.read ctx = .inr (TypedIR.eval buf ctx) := ihBuf b seenBuf
    have readOffset : o.read ctx = .inl (TypedIR.eval offset ctx) := ihOffset o seenOffset
    have readSize : n.read ctx = .inl (TypedIR.eval size ctx) := ihSize n seenSize
    simp only [ObservationSound, Observation.read, TypedIR.eval, readBuf, readOffset, readSize, asBytes, asInt]
  | _ =>
    first
    | rename_i left right ihLeft ihRight
      have ⟨l, lSeen, mapped⟩ := Option.bind_eq_some_iff.mp found
      have ⟨r, rSeen, result⟩ := Option.map_eq_some_iff.mp mapped
      cases result
      have readLeft : l.read ctx = .inl (TypedIR.eval left ctx) := ihLeft l lSeen
      have readRight : r.read ctx = .inl (TypedIR.eval right ctx) := ihRight r rSeen
      simp only [ObservationSound, Observation.read, TypedIR.eval, readLeft, readRight, asInt]
    | simp_all [ObservationSound, TypedIR.eval] <;> cases found <;> rfl

private theorem integer_observation_sound (expr : Expr .integer) (ctx : Context)
    (obs : Observation) (found : observation expr = some obs) :
    obs.integer ctx = TypedIR.eval expr ctx :=
  congrArg asInt (show obs.read ctx = .inl (TypedIR.eval expr ctx) from observation_sound expr ctx obs found)

inductive IntegerTest where
  | equal : Int → IntegerTest
  | different : Int → IntegerTest
  | lower : Int → IntegerTest
  | upper : Int → IntegerTest

def IntegerTest.holds (value : Int) : IntegerTest → Prop
  | .equal constant => value = constant
  | .different constant => value ≠ constant
  | .lower bound => bound ≤ value
  | .upper bound => value ≤ bound

def IntegerTest.clash : IntegerTest → IntegerTest → Bool
  | .equal a, .equal b => decide (a ≠ b)
  | .equal a, .different b | .different a, .equal b => decide (a = b)
  | .equal a, .lower b => decide (a < b)
  | .equal a, .upper b => decide (b < a)
  | .lower a, .equal b => decide (b < a)
  | .lower a, .upper b => decide (b < a)
  | .upper a, .equal b => decide (a < b)
  | .upper a, .lower b => decide (a < b)
  | _, _ => false

theorem IntegerTest.clash_sound (left right : IntegerTest) (value : Int)
    (clash : left.clash right = true) (a : left.holds value) (b : right.holds value) :
    False := by
  cases left <;> cases right <;>
    simp only [IntegerTest.clash, IntegerTest.holds, decide_eq_true_eq] at * <;>
    first | contradiction | omega

inductive Fact where
  | integer : Observation → IntegerTest → Fact
  | text : InputSlot → String → Fact
  | boolean : InputSlot → Bool → Fact

def Fact.holds (ctx : Context) : Fact → Prop
  | .integer observation test => test.holds (observation.integer ctx)
  | .text slot value => slot.read .text ctx = value
  | .boolean slot value => slot.read .boolean ctx = value

private def integerFacts (expr : Expr .integer) (test : IntegerTest) : List Fact :=
  match observation expr with
  | some observation => [.integer observation test]
  | none => []

private theorem integerFacts_sound (expr : Expr .integer) (test : IntegerTest) (ctx : Context)
    (valid : test.holds (TypedIR.eval expr ctx)) (fact : Fact) (member : fact ∈ integerFacts expr test) :
    fact.holds ctx := by
  cases found : observation expr with
  | none => simp [integerFacts, found] at member
  | some observation =>
    simp only [integerFacts, found, List.mem_singleton] at member
    subst fact
    change test.holds (observation.integer ctx)
    rw [integer_observation_sound expr ctx observation found]
    exact valid

def facts {kind : Kind} (guard : Expr kind) : List Fact :=
  match guard with
  | .boolAnd left right => facts left ++ facts right
  | .equal .integer expr (.literal _ value) => integerFacts expr (.equal value)
  | .intGe expr (.literal _ value) => integerFacts expr (.lower value)
  | .intLe expr (.literal _ value) => integerFacts expr (.upper value)
  | .notEqual .integer expr (.literal _ value)
  | .boolNot (.equal .integer expr (.literal _ value)) => integerFacts expr (.different value)
  | .boolNot (.intGe expr (.literal _ value)) => integerFacts expr (.upper (value - 1))
  | .boolNot (.intLe expr (.literal _ value)) => integerFacts expr (.lower (value + 1))
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
  | case2 expr value =>
    exact integerFacts_sound expr (.equal value) ctx
      (show TypedIR.eval expr ctx = value from of_decide_eq_true enabled) fact member
  | case3 expr value =>
    exact integerFacts_sound expr (.lower value) ctx
      (show value ≤ TypedIR.eval expr ctx from of_decide_eq_true enabled) fact member
  | case4 expr value =>
    exact integerFacts_sound expr (.upper value) ctx
      (show TypedIR.eval expr ctx ≤ value from of_decide_eq_true enabled) fact member
  | case5 expr value =>
    apply integerFacts_sound expr (.different value) ctx _ fact member
    change !(decide (TypedIR.eval expr ctx = value)) = true at enabled
    simpa [IntegerTest.holds] using enabled
  | case6 expr value =>
    apply integerFacts_sound expr (.different value) ctx _ fact member
    change !(decide (TypedIR.eval expr ctx = value)) = true at enabled
    simpa [IntegerTest.holds] using enabled
  | case7 expr value =>
    apply integerFacts_sound expr (.upper (value - 1)) ctx _ fact member
    change !(decide (value ≤ TypedIR.eval expr ctx)) = true at enabled
    have bound : ¬ value ≤ TypedIR.eval expr ctx := by simpa using enabled
    change TypedIR.eval expr ctx ≤ value - 1
    exact Int.le_sub_one_of_lt (Int.lt_of_not_ge bound)
  | case8 expr value =>
    apply integerFacts_sound expr (.lower (value + 1)) ctx _ fact member
    change !(decide (TypedIR.eval expr ctx ≤ value)) = true at enabled
    have bound : ¬ TypedIR.eval expr ctx ≤ value := by simpa using enabled
    change value + 1 ≤ TypedIR.eval expr ctx
    exact Int.add_one_le_of_lt (Int.lt_of_not_ge bound)
  | _ =>
    simp_all [Enabled, TypedIR.eval, equalValue, Fact.holds, InputSlot.read] <;>
      exact of_decide_eq_true enabled

def Fact.clash : Fact → Fact → Bool
  | .integer x a, .integer y b => decide (x = y) && a.clash b
  | .text x a, .text y b => decide (x = y ∧ a ≠ b)
  | .boolean x a, .boolean y b => decide (x = y ∧ a ≠ b)
  | _, _ => false

theorem Fact.clash_sound (left right : Fact) (ctx : Context)
    (clash : left.clash right = true) (a : left.holds ctx) (b : right.holds ctx) : False := by
  cases left <;> cases right <;> simp only [Fact.clash, Bool.and_eq_true, decide_eq_true_eq] at clash
  all_goals
    first
    | contradiction
    | obtain ⟨rfl, incompatible⟩ := clash
      exact IntegerTest.clash_sound _ _ _ incompatible a b
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
