import TCPIPClosedCore
namespace TCPIPClosedTransitions
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts
open EffectConditions EffectFootprint TimedObligations TCPIPSendWire GuardedSuffix
set_option maxRecDepth 16384

theorem close_111 : Approved.raw_111_external :=
  close_checked rule_111 none false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_111 none (fixedText e579) none rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_112 : Approved.raw_112_external :=
  close_checked rule_112 none false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_112 none (fixedText e568) none rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_165 : Approved.raw_165_timer_4 :=
  close_checked rule_165 (some 4) false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_165 (some 4) (fixedText e568) none rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_166 : Approved.raw_166_timer_4 :=
  close_checked rule_166 (some 4) false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_166 (some 4) (fixedText e740) none rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_167 : Approved.raw_167_timer_4 :=
  close_checked rule_167 (some 4) false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_167 (some 4) (fixedText e940) none rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_168 : Approved.raw_168_timer_4 :=
  close_checked rule_168 (some 4) false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_168 (some 4) (fixedText e958) none rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_169 : Approved.raw_169_timer_4 :=
  close_checked rule_169 (some 4) false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_169 (some 4) (fixedText e961) none rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_170 : Approved.raw_170_timer_4 :=
  close_checked rule_170 (some 4) false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_170 (some 4) (fixedText e947) none rfl (by decide) rfl)
    (by intro impossible; cases impossible)


end TCPIPClosedTransitions
