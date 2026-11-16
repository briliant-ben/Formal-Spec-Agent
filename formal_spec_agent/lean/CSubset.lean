import Foundation

/- A pure C-expression value model under pinned runtime/ABI contracts.
   No C memory, compiler, EFSM scheduling, mutation, or failure semantics. -/
namespace FormalSpecAgent.CSubset

inductive Kind where
  | integer | boolean | bytes

abbrev Value : Kind → Type
  | .integer => Int
  | .boolean => Bool
  | .bytes => Bytes

structure Context where
  integers : Nat → Int
  booleans : Nat → Bool
  buffers : Nat → Bytes

def NativeContext (ctx : Context) : Prop :=
  (∀ n, (ctx.buffers n).length ≤ 4096) ∧
  (∀ n, -(2^63 : Int) ≤ ctx.integers n ∧ ctx.integers n < (2^63 : Int))

inductive IRExpr : Kind → Type where
  | integer : Int → IRExpr .integer
  | boolean : Bool → IRExpr .boolean
  | intField : Nat → IRExpr .integer
  | boolField : Nat → IRExpr .boolean
  | bytesField : Nat → IRExpr .bytes
  | read : IRExpr .bytes → IRExpr .integer → IRExpr .integer
  | choose {k : Kind} : IRExpr .boolean → IRExpr k → IRExpr k → IRExpr k

inductive CExpr : Kind → Type where
  | integer : Int → CExpr .integer
  | boolean : Bool → CExpr .boolean
  | intSlot : Nat → CExpr .integer
  | boolSlot : Nat → CExpr .boolean
  | bytesSlot : Nat → CExpr .bytes
  | callRead : CExpr .bytes → CExpr .integer → CExpr .integer
  | conditional {k : Kind} : CExpr .boolean → CExpr k → CExpr k → CExpr k

/- Mathematical contract of the pinned byte_at_or_zero helper on admitted
   buffers/indices. Its explicit upper guard differs from IR's default lookup.
   Native memory access and signed/unsigned ABI interpretation are trusted. -/
def cRead (xs : Bytes) (i : Int) : Int :=
  if i < 0 then 0
  else if xs.length ≤ i.toNat then 0
  else Int.ofNat (xs.getD i.toNat 0).val

def evalIR {k : Kind} (e : IRExpr k) (ctx : Context) : Value k :=
  match e with
  | .integer n => n
  | .boolean b => b
  | .intField n => ctx.integers n
  | .boolField n => ctx.booleans n
  | .bytesField n => ctx.buffers n
  | .read b i => byteAt (evalIR b ctx) (evalIR i ctx)
  | .choose b t f => if evalIR b ctx then evalIR t ctx else evalIR f ctx

def lower {k : Kind} (e : IRExpr k) : CExpr k :=
  match e with
  | .integer n => .integer n
  | .boolean b => .boolean b
  | .intField n => .intSlot n
  | .boolField n => .boolSlot n
  | .bytesField n => .bytesSlot n
  | .read b i => .callRead (lower b) (lower i)
  | .choose b t f => .conditional (lower b) (lower t) (lower f)

def evalC {k : Kind} (e : CExpr k) (ctx : Context) : Value k :=
  match e with
  | .integer n => n
  | .boolean b => b
  | .intSlot n => ctx.integers n
  | .boolSlot n => ctx.booleans n
  | .bytesSlot n => ctx.buffers n
  | .callRead b i => cRead (evalC b ctx) (evalC i ctx)
  | .conditional b t f => if evalC b ctx then evalC t ctx else evalC f ctx

end FormalSpecAgent.CSubset
