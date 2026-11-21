import TCPIPTransmitCertificate

namespace TCPIPTransmit
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts TCPIPTransmitFacts
open EffectConditions EffectFootprint GuardedSuffix TimedObligations TCPIPSendWire
set_option maxRecDepth 16384

theorem first_empty : Approved.raw_241_external :=
  certify true .empty rfl rfl (by decide +kernel) rfl rfl rfl

theorem first_pending : Approved.raw_242_external :=
  certify true .pending rfl rfl (by decide +kernel) rfl rfl rfl

theorem first_resolved : Approved.raw_243_external :=
  certify true .resolved rfl rfl (by decide +kernel) rfl rfl rfl

theorem continued_empty : Approved.raw_244_external :=
  certify false .empty rfl rfl (by decide +kernel) rfl rfl rfl

theorem continued_pending : Approved.raw_245_external :=
  certify false .pending rfl rfl (by decide +kernel) rfl rfl rfl

theorem continued_resolved : Approved.raw_246_external :=
  certify false .resolved rfl rfl (by decide +kernel) rfl rfl rfl

def firings : List (Rule × Option Nat) :=
  [(rule_241, none), (rule_242, none), (rule_243, none),
   (rule_244, none), (rule_245, none), (rule_246, none)]

theorem checked : Each (fun p => FiringPreserves model p.1 p.2) firings :=
  ⟨first_empty, first_pending, first_resolved, continued_empty, continued_pending,
   continued_resolved, trivial⟩

private theorem transmitMember (index : Nat) (r : Rule)
    (selected : model.rules[index]? = some r) (external : r.event ∈ model.externalEvents) :
    (r, none) ∈ rawChecks model declaredTimers :=
  raw_external_member model declaredTimers r (List.mem_iff_getElem?.mpr ⟨index, selected⟩) external

theorem members : Each (fun p => p ∈ rawChecks model declaredTimers) firings :=
  ⟨transmitMember 241 rule_241 rfl (by decide), transmitMember 242 rule_242 rfl (by decide),
   transmitMember 243 rule_243 rfl (by decide), transmitMember 244 rule_244 rfl (by decide),
   transmitMember 245 rule_245 rfl (by decide), transmitMember 246 rule_246 rfl (by decide), trivial⟩

end TCPIPTransmit
