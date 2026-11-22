import TypedContracts

open FormalSpecAgent.TypedIR FormalSpecAgent.TypedMachine
open FormalSpecAgent.TypedContracts

namespace Controller

def badRule : Rule :=
  { id := 0, source := 0, target := 0, event := 0,
    guard := .literal .boolean true,
    actions := [.assign .integer 0 (.literal .integer (-1))] }

def badModel : Model :=
  { rules := [badRule],
    invariants := [.intGe (.variable .integer 0) (.literal .integer 0)],
    timerEvents := fun _ => 0, externalEvents := [0] }

def initial : Snapshot := { values := zeroValues, state := 0, now := 0, timers := [] }
def rejected : Transition :=
  { after := { initial with values := setValue .integer 0 (-1) zeroValues },
    rule := 0, event := 0, fields := zeroValues, emitted := [] }

theorem bad_candidate_is_not_filtered : candidate initial badRule zeroValues 0 none = .ok rejected := by
  rfl

theorem runtime_filter_hides_bad_candidate : runRule badModel initial badRule zeroValues 0 none = .error .invariant := by
  rfl

theorem before_filter_property_rejects_bad_write : ¬RulePreserves badModel badRule := by
  intro preserve
  obtain ⟨t, executed, final⟩ := preserve initial zeroValues (by rfl) (by rfl) (by rfl)
  change candidate initial badRule zeroValues 0 none = .ok t at executed
  rw [bad_candidate_is_not_filtered] at executed
  have equal : rejected = t := Except.ok.inj executed
  subst t
  change false = true at final
  cases final

def noEvents : Model :=
  { rules := [], invariants := [], timerEvents := fun _ => 0, externalEvents := [] }

theorem coverage_only_declared_events : Covers noEvents [0] := by
  intro snapshot event fields hstate hevent hinv
  simp [noEvents] at hevent

end Controller

#print axioms FormalSpecAgent.TypedContracts.candidate
#print axioms FormalSpecAgent.TypedContracts.runRule_eq_filter
#print axioms FormalSpecAgent.TypedContracts.preserving_rule_succeeds
#print axioms Controller.before_filter_property_rejects_bad_write
#print axioms Controller.coverage_only_declared_events
