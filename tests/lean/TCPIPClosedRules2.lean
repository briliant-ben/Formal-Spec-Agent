import TCPIPClosedCore
namespace TCPIPClosedTransitions
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts
open EffectConditions EffectFootprint TimedObligations TCPIPSendWire GuardedSuffix
set_option maxRecDepth 16384

theorem close_198 : Approved.raw_198_external :=
  close_checked rule_198 none true rfl rfl (fun _ _ => rfl) rfl
    (fun _ _ _ _ => rfl) (fun _ => rfl)

theorem close_199 : Approved.raw_199_external :=
  close_checked rule_199 none false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_199 none (fixedText e940) (some e1097) rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_200 : Approved.raw_200_external :=
  close_checked rule_200 none false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_200 none (fixedText e958) (some e1097) rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_201 : Approved.raw_201_external :=
  close_checked rule_201 none false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_201 none (fixedText e943) (some e1097) rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_202 : Approved.raw_202_external :=
  close_checked rule_202 none false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_202 none (fixedText e961) (some e1097) rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_203 : Approved.raw_203_external :=
  close_checked rule_203 none false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_203 none (fixedText e947) (some e1097) rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_204 : Approved.raw_204_external :=
  close_checked rule_204 none false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_204 none (fixedText e966) (some e1097) rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_207 : Approved.raw_207_external :=
  close_checked rule_207 none false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_207 none (fixedText e568) (some e1120) rfl (by decide) rfl)
    (by intro impossible; cases impossible)


end TCPIPClosedTransitions
