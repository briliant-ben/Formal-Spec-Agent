import ScheduledPreservation
import Counterexample
open FormalSpecAgent.ScheduledPreservation
open Controller
namespace ScheduledController

theorem raw_obligation_rejects_filtered_timer_loss :
    ¬MatchingRaw activeInvariant 0 (some 0) := by
  intro matching
  have member : noRearm ∈ activeInvariant.rules := by simp [activeInvariant]
  exact removing_active_timer_violates_raw_preservation (matching noRearm member (by rfl))

end ScheduledController
#print axioms FormalSpecAgent.ScheduledPreservation.MatchingRaw
#print axioms FormalSpecAgent.ScheduledPreservation.fire_success_invariant_from_raw
#print axioms FormalSpecAgent.ScheduledPreservation.external_success_invariant_from_raw
#print axioms FormalSpecAgent.ScheduledPreservation.timer_success_invariant_from_raw
#print axioms ScheduledController.raw_obligation_rejects_filtered_timer_loss
