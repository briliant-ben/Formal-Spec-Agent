import StateSubset

/- Timer-free integer EFSM proof view. Protocol rules remain in IR data.
   Preservation checks the tentative poststate, not a filtered dispatcher. -/
namespace FormalSpecAgent.EfsmSubset
open FormalSpecAgent.StateSubset

inductive Predicate where
  | literal : Bool → Predicate
  | atState : Nat → Predicate
  | equal : IntegerExpr → IntegerExpr → Predicate
  | lessEqual : IntegerExpr → IntegerExpr → Predicate
  | conjunction : Predicate → Predicate → Predicate
  | disjunction : Predicate → Predicate → Predicate
  | negation : Predicate → Predicate

def evalPredicate (p : Predicate) (state : Nat) (s env : List Int) : Bool :=
  match p with
  | .literal b => b
  | .atState n => decide (state = n)
  | .equal a b => decide (evalInteger a s env = evalInteger b s env)
  | .lessEqual a b => decide (evalInteger a s env ≤ evalInteger b s env)
  | .conjunction a b => evalPredicate a state s env && evalPredicate b state s env
  | .disjunction a b => evalPredicate a state s env || evalPredicate b state s env
  | .negation a => !(evalPredicate a state s env)

structure Rule where
  source : Nat
  target : Nat
  event : Nat
  guard : Predicate
  actions : List Action

def invariantsHold (invariants : List Predicate) (state : Nat) (s : List Int) : Bool :=
  invariants.all (fun p => evalPredicate p state s [])

def guardHolds (r : Rule) (s env : List Int) : Bool :=
  evalPredicate r.guard r.source s env

def candidate (r : Rule) (s env : List Int) : Nat × (List Int × Output) :=
  (r.target, work r.actions s env [])

def covered (guards : List Predicate) (state : Nat) (s env : List Int) : Bool :=
  guards.any (fun p => evalPredicate p state s env)

end FormalSpecAgent.EfsmSubset
