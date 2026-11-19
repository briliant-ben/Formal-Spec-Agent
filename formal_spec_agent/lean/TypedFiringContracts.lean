import TypedContracts

namespace FormalSpecAgent.TypedFiringContracts

open FormalSpecAgent.TypedMachine
open FormalSpecAgent.TypedIR
open FormalSpecAgent.TypedContracts

/-- FiringPreserves: raw preservation allowing an optional timer firing to be
removed before candidate. Mirrors RulePreserves, but with firing parameter. -/
def FiringPreserves (model : Model) (rule : Rule) (firing : Option Nat) : Prop :=
  ∀ (snapshot : Snapshot) (fields : Values),
    invariantsHold model snapshot = true →
    snapshot.state = rule.source →
    eval snapshot fields rule.guard = true →
    ∃ t : Transition,
      candidate snapshot rule fields rule.event firing = .ok t ∧
      invariantsHold model t.after = true

/-- none_equivalence: FiringPreserves with none equals RulePreserves. -/
theorem none_equivalence (model : Model) (rule : Rule) :
    FiringPreserves model rule none ↔ RulePreserves model rule := by
  rfl

/-- eval_clock_irrelevant: expression evaluation does not depend on snapshot.now. -/
theorem eval_clock_irrelevant {k : Kind} (e : Expr k) (snapshot : Snapshot) (fields : Values) (now : Int) :
    eval snapshot fields e = eval { snapshot with now := now } fields e := by
  rfl

/-- invariants_clock_irrelevant: invariant satisfaction does not depend on now. -/
theorem invariants_clock_irrelevant (model : Model) (snapshot : Snapshot) (now : Int) :
    invariantsHold model snapshot = invariantsHold model { snapshot with now := now } := by
  rfl

/-- preserving_firing_succeeds: FiringPreserves plus initial facts yields actual runRule success. -/
theorem preserving_firing_succeeds (model : Model) (rule : Rule) (snapshot : Snapshot)
    (fields : Values) (firing : Option Nat) :
    FiringPreserves model rule firing →
    invariantsHold model snapshot = true →
    snapshot.state = rule.source →
    eval snapshot fields rule.guard = true →
    ∃ t : Transition,
      runRule model snapshot rule fields rule.event firing = .ok t ∧
      invariantsHold model t.after = true := by
  intro hPres hInv hSrc hGuard
  have hRaw : ∃ t : Transition,
      candidate snapshot rule fields rule.event firing = .ok t ∧
      invariantsHold model t.after = true :=
    hPres snapshot fields hInv hSrc hGuard
  rcases hRaw with ⟨t, hcand, hAfter⟩
  have hrun : runRule model snapshot rule fields rule.event firing = .ok t := by
    rw [runRule_eq_filter]
    rw [hcand]
    simp [hAfter]
  exact ⟨t, hrun, hAfter⟩

/-- fire_singleton_succeeds: if enabled yields exactly [rule] and FiringPreserves holds,
then actual fire succeeds and final invariant holds. -/
theorem fire_singleton_succeeds (model : Model) (snapshot : Snapshot) (event : Nat)
    (fields : Values) (firing : Option Nat) (rule : Rule) :
    enabled model snapshot event fields = [rule] →
    FiringPreserves model rule firing →
    invariantsHold model snapshot = true →
    snapshot.state = rule.source →
    eval snapshot fields rule.guard = true →
    ∃ t : Transition,
      fire model snapshot event fields firing = .ok t ∧
      invariantsHold model t.after = true := by
  intro hEnabled hPres hInv hSrc hGuard
  have hmem : rule ∈ enabled model snapshot event fields := by
    rw [hEnabled]
    exact List.mem_singleton_self rule
  have selected := (List.mem_filter.mp hmem).2
  simp only [Bool.and_eq_true, beq_iff_eq] at selected
  have hEvent : rule.event = event := selected.1.2
  obtain ⟨t, hrun, hafter⟩ := preserving_firing_succeeds model rule snapshot fields firing hPres hInv hSrc hGuard
  refine ⟨t, ?_, hafter⟩
  unfold fire
  rw [hEnabled]
  simpa only [hEvent] using hrun

end FormalSpecAgent.TypedFiringContracts