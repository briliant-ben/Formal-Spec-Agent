import ValueOps

/- Typed pure expression semantics for the compact IPv4 case's IR operators.
   This is not a transition dispatcher, native memory model or scheduler. -/
namespace FormalSpecAgent.TypedIR

inductive Kind where
  | integer | boolean | text | octets | sequence

abbrev Value : Kind → Type
  | .integer => Int
  | .boolean => Bool
  | .text => String
  | .octets => Bytes
  | .sequence => ValueOps.Seq32

structure Values where
  integers : Nat → Int
  booleans : Nat → Bool
  texts : Nat → String
  buffers : Nat → Bytes
  sequences : Nat → ValueOps.Seq32

def getValue (k : Kind) (v : Values) (n : Nat) : Value k :=
  match k with
  | .integer => v.integers n
  | .boolean => v.booleans n
  | .text => v.texts n
  | .octets => v.buffers n
  | .sequence => v.sequences n

structure Context where
  store : Values
  fields : Values
  state : Nat
  activeTimers : List Nat

def equalValue (k : Kind) (a b : Value k) : Bool :=
  match k with
  | .integer => decide (a = b)
  | .boolean => decide (a = b)
  | .text => decide (a = b)
  | .octets => decide (a = b)
  | .sequence => decide (a = b)

inductive Expr : Kind → Type where
  | literal (k : Kind) : Value k → Expr k
  | variable (k : Kind) : Nat → Expr k
  | field (k : Kind) : Nat → Expr k
  | stateIs : Nat → Expr .boolean
  | timerActive : Nat → Expr .boolean
  | equal (k : Kind) : Expr k → Expr k → Expr .boolean
  | notEqual (k : Kind) : Expr k → Expr k → Expr .boolean
  | choose (k : Kind) : Expr .boolean → Expr k → Expr k → Expr k
  | boolAnd : Expr .boolean → Expr .boolean → Expr .boolean
  | boolOr : Expr .boolean → Expr .boolean → Expr .boolean
  | boolNot : Expr .boolean → Expr .boolean
  | implies : Expr .boolean → Expr .boolean → Expr .boolean
  | add : Expr .integer → Expr .integer → Expr .integer
  | mul : Expr .integer → Expr .integer → Expr .integer
  | sub : Expr .integer → Expr .integer → Expr .integer
  | minimum : Expr .integer → Expr .integer → Expr .integer
  | intLe : Expr .integer → Expr .integer → Expr .boolean
  | intGe : Expr .integer → Expr .integer → Expr .boolean
  | seqAdd : Expr .sequence → Expr .integer → Expr .sequence
  | seqDistance : Expr .sequence → Expr .sequence → Expr .integer
  | seqComparable : Expr .sequence → Expr .sequence → Expr .boolean
  | seqLt : Expr .sequence → Expr .sequence → Expr .boolean
  | seqLe : Expr .sequence → Expr .sequence → Expr .boolean
  | bytesLength : Expr .octets → Expr .integer
  | concat : Expr .octets → Expr .octets → Expr .octets
  | slice : Expr .octets → Expr .integer → Expr .integer → Expr .octets
  | byteAt : Expr .octets → Expr .integer → Expr .integer
  | pack8 : Expr .integer → Expr .octets
  | pack16 : Expr .integer → Expr .octets
  | pack32 : Expr .integer → Expr .octets
  | checksum : Expr .octets → Expr .integer

def eval {k : Kind} (e : Expr k) (ctx : Context) : Value k :=
  match e with
  | .literal _ v => v
  | .variable k n => getValue k ctx.store n
  | .field k n => getValue k ctx.fields n
  | .stateIs n => decide (ctx.state = n)
  | .timerActive n => decide (n ∈ ctx.activeTimers)
  | .equal k a b => equalValue k (eval a ctx) (eval b ctx)
  | .notEqual k a b => !(equalValue k (eval a ctx) (eval b ctx))
  | .choose _ b t f => if eval b ctx then eval t ctx else eval f ctx
  | .boolAnd a b => eval a ctx && eval b ctx
  | .boolOr a b => eval a ctx || eval b ctx
  | .boolNot a => !(eval a ctx)
  | .implies a b => !(eval a ctx) || eval b ctx
  | .add a b => eval a ctx + eval b ctx
  | .mul a b => eval a ctx * eval b ctx
  | .sub a b => eval a ctx - eval b ctx
  | .minimum a b => min (eval a ctx) (eval b ctx)
  | .intLe a b => decide (eval a ctx ≤ eval b ctx)
  | .intGe a b => decide (eval a ctx ≥ eval b ctx)
  | .seqAdd a b => ValueOps.seqAdd (eval a ctx) (eval b ctx)
  | .seqDistance a b => ValueOps.seqDistance (eval a ctx) (eval b ctx)
  | .seqComparable a b => ValueOps.seqComparable (eval a ctx) (eval b ctx)
  | .seqLt a b => ValueOps.seqLt (eval a ctx) (eval b ctx)
  | .seqLe a b => ValueOps.seqLe (eval a ctx) (eval b ctx)
  | .bytesLength a => Int.ofNat (eval a ctx).length
  | .concat a b => eval a ctx ++ eval b ctx
  | .slice a b c => byteSlice (eval a ctx) (eval b ctx) (eval c ctx)
  | .byteAt a b => FormalSpecAgent.byteAt (eval a ctx) (eval b ctx)
  | .pack8 a => ValueOps.pack8 (eval a ctx)
  | .pack16 a => ValueOps.pack16 (eval a ctx)
  | .pack32 a => ValueOps.pack32 (eval a ctx)
  | .checksum a => ValueOps.checksum (eval a ctx)

end FormalSpecAgent.TypedIR
