import BatchReplay
import MachineObserve
import StoreFacts

namespace FormalSpecAgent.BatchObserve
open TypedMachine MachineObserve TypedIR

structure SeenTransition where
  rule : Nat
  event : Nat
  fields : List Packed
  after : SeenSnapshot
  emitted : List SeenMessage
  deriving DecidableEq

def transition (schema : List (Kind × Nat))
    (eventSchemas : Nat → List (Kind × Nat)) (t : Transition) : SeenTransition :=
  { rule := t.rule, event := t.event,
    fields := (eventSchemas t.event).map fun (k, n) => packed k (getValue k t.fields n),
    after := snapshot schema t.after, emitted := t.emitted.map message }

inductive Outcome where
  | success : SeenSnapshot → List SeenTransition → Outcome
  | error : Fault → SeenSnapshot → Outcome
  deriving DecidableEq

def outcome (schema : List (Kind × Nat)) (eventSchemas : Nat → List (Kind × Nat))
    (initial : Snapshot) (result : Except Fault BatchMachine.Batch) : Outcome :=
  match result with
  | .error fault => .error fault (snapshot schema (BatchMachine.rollback initial result))
  | .ok batch => .success (snapshot schema batch.after)
      (batch.trace.map (transition schema eventSchemas))

end FormalSpecAgent.BatchObserve
