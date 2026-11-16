import Foundation

/- An integer-only, timer-free action-block semantics derived from Protocol IR.
   No guards/selection, native overflow, memory, scheduling or compiler proof. -/
namespace FormalSpecAgent.StateSubset

abbrev Store := List Int
abbrev Environment := List Int
abbrev Output := List (Nat × Int)

inductive IntegerExpr where
  | literal : Int → IntegerExpr
  | variable : Nat → IntegerExpr
  | field : Nat → IntegerExpr

def evalInteger (e : IntegerExpr) (s : Store) (env : Environment) : Int :=
  match e with
  | .literal n => n
  | .variable n => s.getD n 0
  | .field n => env.getD n 0

inductive Predicate where
  | literal : Bool → Predicate
  | equal : IntegerExpr → IntegerExpr → Predicate
  | lessEqual : IntegerExpr → IntegerExpr → Predicate
  | conjunction : Predicate → Predicate → Predicate

def evalPredicate (p : Predicate) (s : Store) : Bool :=
  match p with
  | .literal b => b
  | .equal a b => decide (evalInteger a s [] = evalInteger b s [])
  | .lessEqual a b => decide (evalInteger a s [] ≤ evalInteger b s [])
  | .conjunction a b => evalPredicate a s && evalPredicate b s

inductive Action where
  | assign : Nat → IntegerExpr → Action
  | emit : Nat → IntegerExpr → Action

def work (actions : List Action) (s : Store) (env : Environment)
    (output : Output) : Store × Output :=
  match actions with
  | [] => (s, output)
  | .assign n e :: rest =>
      work rest (s.set n (evalInteger e s env)) env output
  | .emit message e :: rest =>
      work rest s env (output ++ [(message, evalInteger e s env)])

structure Outcome where
  accepted : Bool
  values : Store
  emitted : Output
  deriving DecidableEq

def invariantsHold (invariants : List Predicate) (s : Store) : Bool :=
  invariants.all (fun p => evalPredicate p s)

def execute (actions : List Action) (invariants : List Predicate)
    (initial : Store) (env : Environment) : Outcome :=
  let candidate := work actions initial env []
  if invariantsHold invariants candidate.1 then
    ⟨true, candidate.1, candidate.2⟩
  else
    ⟨false, initial, []⟩

end FormalSpecAgent.StateSubset
