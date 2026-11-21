import TCPIPClosedCore
namespace TCPIPClosedTransitions
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts
open EffectConditions EffectFootprint TimedObligations TCPIPSendWire GuardedSuffix
set_option maxRecDepth 16384

theorem close_171 : Approved.raw_171_timer_3 :=
  close_checked rule_171 (some 3) false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_171 (some 3) (fixedText e966) none rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_172 : Approved.raw_172_external :=
  close_checked rule_172 none false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_172 none (fixedText e14) none rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_173 : Approved.raw_173_external :=
  close_checked rule_173 none false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_173 none (fixedText e579) none rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_174 : Approved.raw_174_external :=
  close_checked rule_174 none false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_174 none (fixedText e568) none rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_190 : Approved.raw_190_external :=
  close_checked rule_190 none false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_190 none (fixedText e961) none rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_191 : Approved.raw_191_external :=
  close_checked rule_191 none false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_191 none (fixedText e947) none rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_192 : Approved.raw_192_external :=
  close_checked rule_192 none false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_192 none (fixedText e966) none rfl (by decide) rfl)
    (by intro impossible; cases impossible)

theorem close_197 : Approved.raw_197_external :=
  close_checked rule_197 none false rfl rfl (fun _ _ => rfl) rfl
    (preserve_empty rule_197 none (fixedText e740) (some e1093) rfl (by decide) rfl)
    (by intro impossible; cases impossible)


end TCPIPClosedTransitions
