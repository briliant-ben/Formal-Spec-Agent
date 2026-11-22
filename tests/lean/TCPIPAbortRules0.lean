import TCPIPAbortCore
namespace TCPIPClosedTransitions
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts
open EffectConditions EffectFootprint TimedObligations TCPIPSendWire GuardedSuffix
set_option maxRecDepth 16384

theorem close_175 : Approved.raw_175_external :=
  abort_checked rule_175 .empty (fixedText e740) false rfl rfl rfl (fun _ _ => rfl)
    ⟨⟨by decide +kernel, by decide +kernel, rfl⟩, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩⟩ (by intro impossible; cases impossible) (by decide +kernel)
    (reset_buffer_empty rule_175 .empty (fixedText e740) (by decide) rfl) (by intro impossible; cases impossible)

theorem close_176 : Approved.raw_176_external :=
  abort_checked rule_176 .pending (fixedText e740) false rfl rfl rfl (fun _ _ => rfl)
    ⟨by decide +kernel, by decide +kernel, rfl⟩ (by intro impossible; cases impossible) (by decide +kernel)
    (reset_buffer_empty rule_176 .pending (fixedText e740) (by decide) rfl) (by intro impossible; cases impossible)

theorem close_177 : Approved.raw_177_external :=
  abort_checked rule_177 .resolved (fixedText e740) false rfl rfl rfl (fun _ _ => rfl)
    trivial (fun _ => rfl) (by decide +kernel)
    (reset_buffer_empty rule_177 .resolved (fixedText e740) (by decide) rfl) (by intro impossible; cases impossible)

theorem close_178 : Approved.raw_178_external :=
  abort_checked rule_178 .empty (fixedText e807) true rfl rfl rfl (fun _ _ => rfl)
    ⟨⟨by decide +kernel, by decide +kernel, rfl⟩, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩⟩ (by intro impossible; cases impossible) (by decide +kernel)
    (fun _ _ _ _ => rfl) (fun _ => rfl)

theorem close_179 : Approved.raw_179_external :=
  abort_checked rule_179 .pending (fixedText e807) true rfl rfl rfl (fun _ _ => rfl)
    ⟨by decide +kernel, by decide +kernel, rfl⟩ (by intro impossible; cases impossible) (by decide +kernel)
    (fun _ _ _ _ => rfl) (fun _ => rfl)


end TCPIPClosedTransitions
