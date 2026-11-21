import TypedFiringContracts
open FormalSpecAgent.TypedMachine FormalSpecAgent.TypedIR
open FormalSpecAgent.TypedContracts FormalSpecAgent.TypedFiringContracts
namespace Controller

def noRearm : Rule :=
  { id := 0, source := 0, target := 0, event := 0,
    guard := .literal .boolean true, actions := [] }
def activeInvariant : Model :=
  { rules := [noRearm], invariants := [.timerActive 0],
    timerEvents := fun _ => 0, externalEvents := [0] }
def initial : Snapshot :=
  { values := zeroValues, state := 0, now := 0, timers := [{timer := 0,due := 0}] }
def removed : Transition :=
  { after := {initial with timers := []},rule := 0,event := 0,
    fields := zeroValues,emitted := [] }

theorem raw_removes_firing_before_actions :
    candidate initial noRearm zeroValues 0 (some 0) = .ok removed := by rfl

theorem runtime_rejects_without_satisfying_raw_property :
    runRule activeInvariant initial noRearm zeroValues 0 (some 0) = .error .invariant := by rfl

theorem removing_active_timer_violates_raw_preservation :
    ¬FiringPreserves activeInvariant noRearm (some 0) := by
  intro preserve
  obtain ⟨t, executed, final⟩ := preserve initial zeroValues (by rfl) (by rfl) (by rfl)
  change candidate initial noRearm zeroValues 0 (some 0) = .ok t at executed
  rw [raw_removes_firing_before_actions] at executed
  have equal : removed = t := Except.ok.inj executed
  subst t
  change false = true at final
  cases final

def rearm : Rule := { noRearm with actions := [.arm 0 (.literal .integer 1)] }
def rearmed : Transition :=
  { after := {initial with timers := [{timer := 0,due := 1}]},rule := 0,event := 0,
    fields := zeroValues,emitted := [] }

theorem raw_rearm_uses_current_firing_clock :
    candidate initial rearm zeroValues 0 (some 0) = .ok rearmed := by rfl

theorem rearmed_invariant_holds :
    invariantsHold activeInvariant rearmed.after = true := by rfl
end Controller
#print axioms Controller.raw_removes_firing_before_actions
#print axioms Controller.runtime_rejects_without_satisfying_raw_property
#print axioms Controller.removing_active_timer_violates_raw_preservation
#print axioms Controller.raw_rearm_uses_current_firing_clock
#print axioms Controller.rearmed_invariant_holds
