import TCPIPClosedCore
namespace TCPIPClosedTransitions
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts
open EffectConditions EffectFootprint TimedObligations TCPIPSendWire GuardedSuffix
set_option maxRecDepth 16384

theorem close_209 : Approved.raw_209_external :=
  close_checked rule_209 none false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_209 none (fixedText e740) (some e1126) rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_210 : Approved.raw_210_external :=
  close_checked rule_210 none true rfl rfl (fun _ _ => rfl) rfl
    (fun _ _ _ _ => rfl) (fun _ => rfl)

theorem close_211 : Approved.raw_211_external :=
  close_checked rule_211 none false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_211 none (fixedText e940) (some e1129) rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_212 : Approved.raw_212_external :=
  close_checked rule_212 none false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_212 none (fixedText e958) (some e1129) rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_213 : Approved.raw_213_external :=
  close_checked rule_213 none false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_213 none (fixedText e943) (some e1129) rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_214 : Approved.raw_214_external :=
  close_checked rule_214 none false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_214 none (fixedText e961) (some e1129) rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_215 : Approved.raw_215_external :=
  close_checked rule_215 none false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_215 none (fixedText e947) (some e1129) rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_216 : Approved.raw_216_external :=
  close_checked rule_216 none false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_216 none (fixedText e966) (some e1129) rfl (by decide) rfl)
    (by intro impossible; cases impossible)


end TCPIPClosedTransitions
