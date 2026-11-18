import BatchPreservation

open FormalSpecAgent.TypedMachine
open FormalSpecAgent.TimerDomain

namespace BatchPreservationAudit

def armRule : Rule :=
  { id := 0, source := 0, target := 0, event := 0,
    guard := .literal .boolean true,
    actions := [.arm 1 (.literal .integer 10)] }

def model : Model :=
  { rules := [armRule], invariants := [], timerEvents := fun _ => 0,
    externalEvents := [0] }

/-- The static obligation rejects an ID outside the supplied IR schema. -/
theorem undeclared_arm_rejected : ¬ArmsDeclared [0] model := by
  intro declared
  have member : 1 ∈ ([0] : List Nat) :=
    declared armRule (by simp [model]) 1 (.literal .integer 10) (by simp [armRule])
  simp at member

end BatchPreservationAudit
#print axioms FormalSpecAgent.TimerDomain.work_declared
#print axioms FormalSpecAgent.TimerDomain.fire_declared
#print axioms FormalSpecAgent.TimerDomain.external_declared
#print axioms FormalSpecAgent.TimerDomain.step_declared
#print axioms FormalSpecAgent.BatchPreservation.advance_from_raw
#print axioms FormalSpecAgent.BatchPreservation.tick_from_raw
#print axioms FormalSpecAgent.BatchPreservation.dispatch_from_raw
#print axioms BatchPreservationAudit.undeclared_arm_rejected
