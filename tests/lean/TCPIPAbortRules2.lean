import TCPIPAbortCore
namespace TCPIPClosedTransitions
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts
open EffectConditions EffectFootprint TimedObligations TCPIPSendWire GuardedSuffix
set_option maxRecDepth 16384

theorem close_185 : Approved.raw_185_external :=
  abort_checked rule_185 .pending (fixedText e958) false rfl rfl rfl (fun _ _ => rfl)
    ⟨by decide +kernel, by decide +kernel, rfl⟩ (by intro impossible; cases impossible) (by decide +kernel)
    (reset_buffer_empty rule_185 .pending (fixedText e958) (by decide) rfl) (by intro impossible; cases impossible)

theorem close_186 : Approved.raw_186_external :=
  abort_checked rule_186 .resolved (fixedText e958) false rfl rfl rfl (fun _ _ => rfl)
    trivial (fun _ => rfl) (by decide +kernel)
    (reset_buffer_empty rule_186 .resolved (fixedText e958) (by decide) rfl) (by intro impossible; cases impossible)

theorem close_187 : Approved.raw_187_external :=
  abort_checked rule_187 .empty (fixedText e943) false rfl rfl rfl (fun _ _ => rfl)
    ⟨⟨by decide +kernel, by decide +kernel, rfl⟩, rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, trivial⟩⟩ (by intro impossible; cases impossible) (by decide +kernel)
    (reset_buffer_empty rule_187 .empty (fixedText e943) (by decide) rfl) (by intro impossible; cases impossible)

theorem close_188 : Approved.raw_188_external :=
  abort_checked rule_188 .pending (fixedText e943) false rfl rfl rfl (fun _ _ => rfl)
    ⟨by decide +kernel, by decide +kernel, rfl⟩ (by intro impossible; cases impossible) (by decide +kernel)
    (reset_buffer_empty rule_188 .pending (fixedText e943) (by decide) rfl) (by intro impossible; cases impossible)

theorem close_189 : Approved.raw_189_external :=
  abort_checked rule_189 .resolved (fixedText e943) false rfl rfl rfl (fun _ _ => rfl)
    trivial (fun _ => rfl) (by decide +kernel)
    (reset_buffer_empty rule_189 .resolved (fixedText e943) (by decide) rfl) (by intro impossible; cases impossible)


end TCPIPClosedTransitions
