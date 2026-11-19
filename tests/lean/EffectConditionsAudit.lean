import EffectConditions
namespace EffectConditionsAudit

open FormalSpecAgent FormalSpecAgent.TypedMachine FormalSpecAgent.TypedIR
open FormalSpecAgent.TypedContracts FormalSpecAgent.TypedFiringContracts FormalSpecAgent.EffectConditions

def sample : Model :=
  { rules := [], invariants := [
      .boolOr (.stateIs 7) (.stateIs 8),
      .timerActive 2,
      .implies (.stateIs 8) (.boolNot (.timerActive 1)),
      .implies (.stateIs 8) (.intGe (.variable .integer 0) (.literal .integer 2)),
      .variable .boolean 0,
      .equal .integer (.field .integer 7) (.literal .integer 0)],
    externalEvents := [], timerEvents := id }

def ordered : Rule :=
  { id := 8, source := 7, target := 8, event := 3,
    guard := .intGe (.field .integer 0) (.literal .integer 2),
    actions := [.assign .integer 0 (.field .integer 0), .arm 2 (.variable .integer 0),
      .assign .boolean 0 (.timerActive 2)] }

theorem ordered_firing : FiringPreserves sample ordered (some 1) := by
  apply preserves
  intro s f _ _ guard
  have bound : 2 ≤ f.integers 0 := of_decide_eq_true guard
  have positive : 1 ≤ f.integers 0 := Int.le_trans (by decide : (1 : Int) ≤ 2) bound
  change (decide (1 ≤ f.integers 0) && (true && (true && (true &&
    ((false || decide (2 ≤ f.integers 0)) && (true && (true && true))))))) = true
  simp [positive, bound]

def before : Snapshot :=
  { values := {zeroValues with booleans := fun _ => true}, state := 7, now := 10,
    timers := [⟨1, 10⟩, ⟨2, 10⟩] }

def fields : Values := { zeroValues with integers := fun slot => if slot = 0 then 2 else 999 }

def wrongOrder : Rule :=
  { ordered with actions := [.arm 2 (.variable .integer 0),
      .assign .integer 0 (.field .integer 0), .assign .boolean 0 (.timerActive 2)] }

theorem wrong_order_rejected :
    invariantsHold sample before = true ∧
    TypedMachine.eval before fields ordered.guard = true ∧
    holds (obligations sample ordered (some 1)) before fields = true ∧
    holds (obligations sample wrongOrder (some 1)) before fields = false ∧
    candidate before wrongOrder fields wrongOrder.event (some 1) = .error .badDelay := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

#print axioms ordered_firing
#print axioms wrong_order_rejected

end EffectConditionsAudit
