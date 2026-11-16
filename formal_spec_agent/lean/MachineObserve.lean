import TypedMachine

/- Finite, complete schema observations of function-valued stores. Nothing here
   supplies expected outputs to the transition implementation. -/
namespace FormalSpecAgent.MachineObserve
open TypedIR TypedMachine

inductive Packed where
  | integer : Int → Packed
  | boolean : Bool → Packed
  | text : String → Packed
  | octets : Bytes → Packed
  | sequence : Nat → Packed
  deriving DecidableEq, Repr

def packed (k : Kind) (v : Value k) : Packed :=
  match k with
  | .integer => .integer v
  | .boolean => .boolean v
  | .text => .text v
  | .octets => .octets v
  | .sequence => .sequence v.val

structure SeenSnapshot where
  state : Nat
  now : Int
  values : List Packed
  timers : List (Nat × Int)
  deriving DecidableEq, Repr

def insertBySlot (entry : Nat × α) : List (Nat × α) → List (Nat × α)
  | [] => [entry]
  | next :: rest => if entry.1 ≤ next.1 then entry :: next :: rest
      else next :: insertBySlot entry rest

def ordered (entries : List (Nat × α)) : List (Nat × α) :=
  entries.foldr insertBySlot []

def snapshot (schema : List (Kind × Nat)) (s : Snapshot) : SeenSnapshot :=
  { state := s.state, now := s.now,
    values := schema.map fun (k, n) => packed k (getValue k s.values n),
    timers := ordered (s.timers.map fun t => (t.timer, t.due)) }

abbrev SeenMessage := Nat × List (Nat × Packed)

def message (m : Message) : SeenMessage :=
  (m.name, ordered (m.fields.map fun f => (f.slot, packed f.kind f.value)))

inductive Outcome where
  | success : Nat → Nat → SeenSnapshot → List SeenMessage → Outcome
  | error : Fault → SeenSnapshot → Outcome
  deriving DecidableEq

def outcome (schema : List (Kind × Nat)) (initial : Snapshot)
    (result : Except Fault Transition) : Outcome :=
  match result with
  | .error fault => .error fault (snapshot schema (rollback initial result))
  | .ok result => .success result.rule result.event (snapshot schema result.after)
      (result.emitted.map message)

end FormalSpecAgent.MachineObserve
