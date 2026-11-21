import TCPIPTransmitFacts
import EffectConditions
import GuardedSuffix
import OctetBounds
import TCPIPSendWire

namespace TCPIPTransmit
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts TCPIPTransmitFacts
open EffectConditions EffectFootprint GuardedSuffix TimedObligations TCPIPSendWire
set_option maxRecDepth 16384

def rule (first : Bool) : LinkPhase → Rule :=
  match first with
  | true => fun phase => match phase with
    | .empty => rule_241 | .pending => rule_242 | .resolved => rule_243
  | false => fun phase => match phase with
    | .empty => rule_244 | .pending => rule_245 | .resolved => rule_246

def prefixActions (r : Rule) := r.actions.dropLast
def cut (r : Rule) : Rule := {r with actions := prefixActions r}

def delays (first : Bool) (phase : LinkPhase) : List (Expr .boolean) :=
  (match phase with | .empty => [.intGe e10 e44] | _ => []) ++
    (if first then [.intGe e566 e44] else [])

def timerClauses : List (Expr .boolean) :=
  [e1631, e1638, e1642, e1646, e1651, e1654, e1657, e1660, e1663, e1666]

def tcpClauses (first : Bool) : List (Expr .boolean) :=
  (if first then timerClauses else []) ++ [e1679, e1687, e1690, e1691, e1698, e1704, e1705]

def sendOctets : Expr .octets := .slice e924 e1 e1230

def reads (first : Bool) : ExprRewrite.Rewrite :=
  { varRead := fun kind slot =>
      match kind with
      | .integer => .variable .integer slot
      | .octets =>
        if slot = 41 then .concat e928 sendOctets else
        if slot = 40 then .slice e924 e1230 e925 else .variable .octets slot
      | .sequence => if slot = 29 then .seqAdd e763 e1230 else .variable .sequence slot
      | .boolean => .variable .boolean slot
      | .text => .variable .text slot
    field := fun kind slot => .literal kind (getValue kind zeroValues slot)
    stateIs := fun id => .literal .boolean (decide (0 = id))
    timerActive := fun owner =>
      if owner = 2 && first then .literal .boolean true else .timerActive owner }

def postChecks (first : Bool) (phase : LinkPhase) (inv : Expr .boolean) : List (Expr .boolean) :=
  (obligationsFor (cut (rule first phase)) none [inv]).drop (delays first phase).length

abbrev Post (s : Snapshot) (f : Values) (first : Bool) (phase : LinkPhase) (inv : Expr .boolean) : Prop :=
  holds (postChecks first phase inv) s f = true


end TCPIPTransmit
