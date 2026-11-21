import TCPIPClosedCore
import TCPIPClosedRules0
import TCPIPClosedRules1
import TCPIPClosedRules2
import TCPIPClosedRules3
import TCPIPAbortCore
import TCPIPAbortRules0
import TCPIPAbortRules1
import TCPIPAbortRules2
import TCPIPPassiveCore
import TCPIPClosedDrops

namespace TCPIPClosedTransitions
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts
open EffectConditions EffectFootprint TimedObligations TCPIPSendWire GuardedSuffix
set_option maxRecDepth 16384

def firings : List (Rule × Option Nat) :=
  [(rule_67, none), (rule_111, none), (rule_112, none), (rule_165, some 4),
   (rule_166, some 4), (rule_167, some 4), (rule_168, some 4), (rule_169, some 4),
   (rule_170, some 4), (rule_171, some 3), (rule_172, none), (rule_173, none),
   (rule_174, none), (rule_175, none), (rule_176, none), (rule_177, none),
   (rule_178, none), (rule_179, none), (rule_180, none), (rule_181, none),
   (rule_182, none), (rule_183, none), (rule_184, none), (rule_185, none),
   (rule_186, none), (rule_187, none), (rule_188, none), (rule_189, none),
   (rule_190, none), (rule_191, none), (rule_192, none), (rule_193, none),
   (rule_196, none), (rule_197, none), (rule_198, none), (rule_199, none),
   (rule_200, none), (rule_201, none), (rule_202, none), (rule_203, none),
   (rule_204, none), (rule_205, none), (rule_207, none), (rule_208, none),
   (rule_209, none), (rule_210, none), (rule_211, none), (rule_212, none),
   (rule_213, none), (rule_214, none), (rule_215, none), (rule_216, none), (rule_279, none), (rule_280, none),
   (rule_281, none), (rule_282, none), (rule_283, none)]

theorem checked : Each (fun p => FiringPreserves model p.1 p.2) firings :=
  ⟨open_passive, close_111, close_112, close_165, close_166,
   close_167, close_168, close_169, close_170, close_171,
   close_172, close_173, close_174, close_175, close_176,
   close_177, close_178, close_179, close_180, close_181,
   close_182, close_183, close_184, close_185, close_186,
   close_187, close_188, close_189, close_190, close_191,
   close_192, ignore_reset_closed, reset_passive, close_197, close_198,
   close_199, close_200, close_201, close_202, close_203,
   close_204, ignore_reset_ack_closed, close_207, reset_ack_passive, close_209,
   close_210, close_211, close_212, close_213, close_214,
   close_215, close_216,
   drop_short_closed, drop_ip_length_closed, drop_ip_checksum_closed, drop_tcp_length_closed,
   drop_tcp_checksum_closed, trivial⟩

private theorem externalMember (index : Nat) (r : Rule)
    (selected : model.rules[index]? = some r) (external : r.event ∈ model.externalEvents) :
    (r, none) ∈ rawChecks model declaredTimers :=
  raw_external_member model declaredTimers r (List.mem_iff_getElem?.mpr ⟨index, selected⟩) external

private theorem timerMember (index : Nat) (r : Rule) (timer : Nat)
    (selected : model.rules[index]? = some r) (declared : timer ∈ declaredTimers)
    (trigger : r.event = model.timerEvents timer) : (r, some timer) ∈ rawChecks model declaredTimers :=
  raw_timer_member model declaredTimers r timer (List.mem_iff_getElem?.mpr ⟨index, selected⟩) declared trigger

theorem members : Each (fun p => p ∈ rawChecks model declaredTimers) firings :=
  ⟨externalMember 67 rule_67 rfl (by decide), externalMember 111 rule_111 rfl (by decide),
   externalMember 112 rule_112 rfl (by decide), timerMember 165 rule_165 4 rfl (by decide) rfl,
   timerMember 166 rule_166 4 rfl (by decide) rfl, timerMember 167 rule_167 4 rfl (by decide) rfl,
   timerMember 168 rule_168 4 rfl (by decide) rfl, timerMember 169 rule_169 4 rfl (by decide) rfl,
   timerMember 170 rule_170 4 rfl (by decide) rfl, timerMember 171 rule_171 3 rfl (by decide) rfl,
   externalMember 172 rule_172 rfl (by decide), externalMember 173 rule_173 rfl (by decide),
   externalMember 174 rule_174 rfl (by decide), externalMember 175 rule_175 rfl (by decide),
   externalMember 176 rule_176 rfl (by decide), externalMember 177 rule_177 rfl (by decide),
   externalMember 178 rule_178 rfl (by decide), externalMember 179 rule_179 rfl (by decide),
   externalMember 180 rule_180 rfl (by decide), externalMember 181 rule_181 rfl (by decide),
   externalMember 182 rule_182 rfl (by decide), externalMember 183 rule_183 rfl (by decide),
   externalMember 184 rule_184 rfl (by decide), externalMember 185 rule_185 rfl (by decide),
   externalMember 186 rule_186 rfl (by decide), externalMember 187 rule_187 rfl (by decide),
   externalMember 188 rule_188 rfl (by decide), externalMember 189 rule_189 rfl (by decide),
   externalMember 190 rule_190 rfl (by decide), externalMember 191 rule_191 rfl (by decide),
   externalMember 192 rule_192 rfl (by decide), externalMember 193 rule_193 rfl (by decide),
   externalMember 196 rule_196 rfl (by decide), externalMember 197 rule_197 rfl (by decide),
   externalMember 198 rule_198 rfl (by decide), externalMember 199 rule_199 rfl (by decide),
   externalMember 200 rule_200 rfl (by decide), externalMember 201 rule_201 rfl (by decide),
   externalMember 202 rule_202 rfl (by decide), externalMember 203 rule_203 rfl (by decide),
   externalMember 204 rule_204 rfl (by decide), externalMember 205 rule_205 rfl (by decide),
   externalMember 207 rule_207 rfl (by decide), externalMember 208 rule_208 rfl (by decide),
   externalMember 209 rule_209 rfl (by decide), externalMember 210 rule_210 rfl (by decide),
   externalMember 211 rule_211 rfl (by decide), externalMember 212 rule_212 rfl (by decide),
   externalMember 213 rule_213 rfl (by decide), externalMember 214 rule_214 rfl (by decide),
   externalMember 215 rule_215 rfl (by decide), externalMember 216 rule_216 rfl (by decide),
   externalMember 279 rule_279 rfl (by decide), externalMember 280 rule_280 rfl (by decide),
   externalMember 281 rule_281 rfl (by decide), externalMember 282 rule_282 rfl (by decide),
   externalMember 283 rule_283 rfl (by decide), trivial⟩

end TCPIPClosedTransitions
