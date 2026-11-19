import TypedIR

namespace FormalSpecAgent.ExprRewrite
open TypedIR
/-- Replace typed reads while leaving the expression operators unchanged. -/
structure Rewrite where
  varRead : (kind : Kind) → Nat → Expr kind
  field : (kind : Kind) → Nat → Expr kind
  stateIs : Nat → Expr .boolean
  timerActive : Nat → Expr .boolean

def run (mapping : Rewrite) {kind : Kind} (expr : Expr kind) : Expr kind :=
  match expr with
  | .variable k slot => mapping.varRead k slot
  | .field k slot => mapping.field k slot
  | .stateIs id => mapping.stateIs id
  | .timerActive id => mapping.timerActive id
  | .literal k value => .literal k value
  | .equal k l r => .equal k (run mapping l) (run mapping r)
  | .notEqual k l r => .notEqual k (run mapping l) (run mapping r)
  | .choose k c l r => .choose k (run mapping c) (run mapping l) (run mapping r)
  | .boolAnd l r => .boolAnd (run mapping l) (run mapping r)
  | .boolOr l r => .boolOr (run mapping l) (run mapping r)
  | .implies l r => .implies (run mapping l) (run mapping r)
  | .add l r => .add (run mapping l) (run mapping r)
  | .mul l r => .mul (run mapping l) (run mapping r)
  | .sub l r => .sub (run mapping l) (run mapping r)
  | .minimum l r => .minimum (run mapping l) (run mapping r)
  | .intLe l r => .intLe (run mapping l) (run mapping r)
  | .intGe l r => .intGe (run mapping l) (run mapping r)
  | .seqAdd l r => .seqAdd (run mapping l) (run mapping r)
  | .seqDistance l r => .seqDistance (run mapping l) (run mapping r)
  | .seqComparable l r => .seqComparable (run mapping l) (run mapping r)
  | .seqLt l r => .seqLt (run mapping l) (run mapping r)
  | .seqLe l r => .seqLe (run mapping l) (run mapping r)
  | .concat l r => .concat (run mapping l) (run mapping r)
  | .byteAt buf i => .byteAt (run mapping buf) (run mapping i)
  | .slice buf i count => .slice (run mapping buf) (run mapping i) (run mapping count)
  | .boolNot x => .boolNot (run mapping x)
  | .bytesLength x => .bytesLength (run mapping x)
  | .checksum x => .checksum (run mapping x)
  | .pack8 x => .pack8 (run mapping x)
  | .pack16 x => .pack16 (run mapping x)
  | .pack32 x => .pack32 (run mapping x)
termination_by structural expr

/-- Each replacement reads the corresponding value in the new context. -/
structure Interprets (mapping : Rewrite) (before after : Context) : Prop where
  varRead : ∀ k slot, TypedIR.eval (mapping.varRead k slot) before = getValue k after.store slot
  field : ∀ k slot, TypedIR.eval (mapping.field k slot) before = getValue k after.fields slot
  stateIs : ∀ id, TypedIR.eval (mapping.stateIs id) before = decide (after.state = id)
  timerActive : ∀ id, TypedIR.eval (mapping.timerActive id) before = decide (id ∈ after.activeTimers)

theorem sound (mapping : Rewrite) (before after : Context)
    (interprets : Interprets mapping before after) {kind : Kind} (expr : Expr kind) :
    TypedIR.eval (run mapping expr) before = TypedIR.eval expr after := by
  induction expr <;> simp_all [run, TypedIR.eval, interprets.varRead, interprets.field,
    interprets.stateIs, interprets.timerActive]
end FormalSpecAgent.ExprRewrite
