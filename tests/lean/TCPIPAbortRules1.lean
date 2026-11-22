import TCPIPAbortCore
namespace TCPIPClosedTransitions
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts
open EffectConditions EffectFootprint TimedObligations TCPIPSendWire GuardedSuffix
set_option maxRecDepth 16384

theorem close_180 : Approved.raw_180_external :=
  abort_checked rule_180 .resolved (fixedText e807) true rfl rfl rfl (fun _ _ => rfl)
    trivial (fun _ => rfl) (by decide +kernel)
    (fun _ _ _ _ => rfl) (fun _ => rfl)

theorem close_181 : Approved.raw_181_external :=
  abort_checked rule_181 .empty (fixedText e940) false rfl rfl rfl (fun _ _ => rfl)
    ⟨⟨by decide +kernel, by decide +kernel, rfl⟩, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩⟩ (by intro impossible; cases impossible) (by decide +kernel)
    (reset_buffer_empty rule_181 .empty (fixedText e940) (by decide) rfl) (by intro impossible; cases impossible)

theorem close_182 : Approved.raw_182_external :=
  abort_checked rule_182 .pending (fixedText e940) false rfl rfl rfl (fun _ _ => rfl)
    ⟨by decide +kernel, by decide +kernel, rfl⟩ (by intro impossible; cases impossible) (by decide +kernel)
    (reset_buffer_empty rule_182 .pending (fixedText e940) (by decide) rfl) (by intro impossible; cases impossible)

theorem close_183 : Approved.raw_183_external :=
  abort_checked rule_183 .resolved (fixedText e940) false rfl rfl rfl (fun _ _ => rfl)
    trivial (fun _ => rfl) (by decide +kernel)
    (reset_buffer_empty rule_183 .resolved (fixedText e940) (by decide) rfl) (by intro impossible; cases impossible)

theorem close_184 : Approved.raw_184_external :=
  abort_checked rule_184 .empty (fixedText e958) false rfl rfl rfl (fun _ _ => rfl)
    ⟨⟨by decide +kernel, by decide +kernel, rfl⟩, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩⟩ (by intro impossible; cases impossible) (by decide +kernel)
    (reset_buffer_empty rule_184 .empty (fixedText e958) (by decide) rfl) (by intro impossible; cases impossible)


end TCPIPClosedTransitions
