import BatchTotality

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

def timerWithoutRule : Model := { model with rules := [] }

def due : TimerEntry := ⟨0, 0⟩

def before : Snapshot :=
  { state := 0, now := 0, timers := [due], values := zeroValues }

theorem missing_due_timer_rule_rejected :
    ¬FormalSpecAgent.TimedSelection.CoversTimers timerWithoutRule [0] [0] := by
  intro coverage
  obtain ⟨rule, member, _⟩ :=
    coverage before (by simp [before]) (by rfl) due (by simp [before]) (by simp [due])
  simp [timerWithoutRule] at member

end BatchPreservationAudit
#print axioms FormalSpecAgent.TimerDomain.work_declared
#print axioms FormalSpecAgent.TimerDomain.fire_declared
#print axioms FormalSpecAgent.TimerDomain.external_declared
#print axioms FormalSpecAgent.TimerDomain.step_declared
#print axioms FormalSpecAgent.BatchPreservation.advance_from_raw
#print axioms FormalSpecAgent.BatchPreservation.tick_from_raw
#print axioms FormalSpecAgent.BatchPreservation.dispatch_from_raw
#print axioms BatchPreservationAudit.undeclared_arm_rejected

#print axioms FormalSpecAgent.TimedSelection.enabled_singleton
#print axioms FormalSpecAgent.TimedSelection.fire_enabled_from_raw
#print axioms FormalSpecAgent.TimedSelection.timer_enabled_from_contracts
#print axioms FormalSpecAgent.TimedSelection.external_enabled_from_contracts
#print axioms BatchPreservationAudit.missing_due_timer_rule_rejected

#print axioms FormalSpecAgent.BatchTotality.fire_target
#print axioms FormalSpecAgent.BatchTotality.advance_total
#print axioms FormalSpecAgent.BatchTotality.tick_total
#print axioms FormalSpecAgent.BatchTotality.dispatch_total
