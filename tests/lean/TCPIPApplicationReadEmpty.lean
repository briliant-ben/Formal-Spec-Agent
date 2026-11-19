import TCPIPApplicationRead

namespace TCPIPApplicationReadEmpty
set_option maxRecDepth 16384
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts
open EffectConditions EffectFootprint GuardedSuffix TimedObligations TCPIPApplicationRead

-- Certify the queue and wire consequences separately to bound kernel reduction.
private theorem queueBound (s : Snapshot) (f : Values) :
    holds (obligationsFor (cut rule_276) none [e1612]) s f = true := by rfl

private theorem queueOnlyPending (s : Snapshot) (f : Values) :
    holds (obligationsFor (cut rule_276) none [e1614]) s f = true := by rfl

private theorem queuePacket (s : Snapshot) (f : Values) :
    holds (obligationsFor (cut rule_276) none [e1615]) s f = true := by rfl

private theorem packetBound (s : Snapshot) (f : Values) :
    holds (obligationsFor (cut rule_276) none [e1706]) s f = true := by rfl

private theorem packetOwner (s : Snapshot) (f : Values) :
    holds (obligationsFor (cut rule_276) none [e1721]) s f = true := by rfl

set_option maxHeartbeats 1600000 in
theorem receive_empty : Approved.raw_276_external := by
  apply certify rule_276 e16 rfl rfl (by decide +kernel) rfl (fun _ _ => rfl)
  intro s f valid est empty
  have read := after_read s f valid est
  have prior := List.all_eq_true.mp valid e1594 (by rw [model_invariants]; simp)
  change (!TypedMachine.eval s zeroValues e16 || TypedMachine.eval s zeroValues e1593) = true at prior
  have phase : TypedMachine.eval s zeroValues e16 = true := empty
  simp only [phase, Bool.not_true, Bool.false_or] at prior
  change ((TypedMachine.eval s zeroValues e1587 && TypedMachine.eval s zeroValues e1589) &&
    TypedMachine.eval s zeroValues e1592) = true at prior
  simp only [Bool.and_eq_true] at prior
  have mac : TypedMachine.eval s f e1587 = true := prior.1.1
  have cache : TypedMachine.eval s f e1592 = true := prior.2
  refine ⟨rfl, ?_, rfl, rfl, queueBound s f, queueOnlyPending s f, queuePacket s f, rfl,
    read.1, read.2.1, read.2.2.1, packetBound s f, packetOwner s f, trivial⟩
  change (((TypedMachine.eval s f e1587 && true) && TypedMachine.eval s f e1592) && true) = true
  simp [mac, cache]

def firings : List (Rule × Option Nat) := [(rule_276, none), (rule_277, none), (rule_278, none)]

theorem checked : Each (fun p => FiringPreserves model p.1 p.2) firings :=
  ⟨receive_empty, receive_pending, receive_resolved, trivial⟩

private theorem readMember (index : Nat) (rule : Rule)
    (selected : model.rules[index]? = some rule) (external : rule.event ∈ model.externalEvents) :
    (rule, none) ∈ rawChecks model declaredTimers :=
  raw_external_member model declaredTimers rule (List.mem_iff_getElem?.mpr ⟨index, selected⟩) external

theorem members : Each (fun p => p ∈ rawChecks model declaredTimers) firings :=
  ⟨readMember 276 rule_276 rfl (by decide), readMember 277 rule_277 rfl (by decide),
    readMember 278 rule_278 rfl (by decide), trivial⟩

#print axioms receive_empty
end TCPIPApplicationReadEmpty
