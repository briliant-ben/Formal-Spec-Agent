import TypedIR

namespace FormalSpecAgent.TypedMachine

open FormalSpecAgent.TypedIR

structure TimerEntry where
  timer : Nat
  due : Int
  deriving DecidableEq, Repr

structure Snapshot where
  values : Values
  state : Nat
  now : Int
  timers : List TimerEntry

structure FieldExpr where
  slot : Nat
  kind : Kind
  expression : Expr kind

structure FieldValue where
  slot : Nat
  kind : Kind
  value : Value kind

structure Message where
  name : Nat
  fields : List FieldValue

inductive Action where
  | assign (kind : Kind) (slot : Nat) (expr : Expr kind)
  | emit (message : Nat) (fields : List FieldExpr)
  | arm (timer : Nat) (delay : Expr .integer)
  | cancel (timer : Nat)

structure Rule where
  id : Nat
  source : Nat
  target : Nat
  event : Nat
  guard : Expr .boolean
  actions : List Action

structure Model where
  rules : List Rule
  invariants : List (Expr .boolean)
  timerEvents : Nat → Nat
  externalEvents : List Nat

inductive Fault where
  | uncovered
  | conflict
  | badDelay
  | invariant
  | time
  | timerInjection
  | pendingTimer
  | noTimer
  deriving DecidableEq, Repr

structure Transition where
  after : Snapshot
  rule : Nat
  event : Nat
  emitted : List Message

def setValue (k : Kind) (slot : Nat) (v : Value k) (s : Values) : Values :=
  match k with
  | .integer => { s with integers := fun n => if n = slot then v else s.integers n }
  | .boolean => { s with booleans := fun n => if n = slot then v else s.booleans n }
  | .text => { s with texts := fun n => if n = slot then v else s.texts n }
  | .octets => { s with buffers := fun n => if n = slot then v else s.buffers n }
  | .sequence => { s with sequences := fun n => if n = slot then v else s.sequences n }

def context (snapshot : Snapshot) (fields : Values) : Context :=
  { store := snapshot.values, fields := fields, state := snapshot.state,
    activeTimers := snapshot.timers.map TimerEntry.timer }

def cancelTimer (snapshot : Snapshot) (timer : Nat) : Snapshot :=
  { snapshot with timers := snapshot.timers.filter (fun te => te.timer != timer) }

def armTimer (snapshot : Snapshot) (timer : Nat) (delay : Int) : Except Fault Snapshot :=
  if delay <= 0 then .error .badDelay
  else
    let timers' := snapshot.timers.filter (fun te => te.timer != timer)
    .ok { snapshot with timers := timers' ++ [{ timer := timer, due := snapshot.now + delay }] }

def eval (snapshot : Snapshot) (fields : Values) {k : Kind} (e : Expr k) : Value k :=
  TypedIR.eval e (context snapshot fields)

def work (actions : List Action) (snapshot : Snapshot) (fields : Values)
    (out : List Message) : Except Fault (Snapshot × List Message) :=
  match actions with
  | [] => .ok (snapshot, out)
  | a :: rest =>
    match a with
    | .assign k slot expr =>
      let v := eval snapshot fields expr
      work rest { snapshot with values := setValue k slot v snapshot.values } fields out
    | .emit name fexprs =>
      let fvals : List FieldValue := fexprs.map (fun fe => { slot := fe.slot, kind := fe.kind, value := eval snapshot fields fe.expression })
      let msg : Message := { name := name, fields := fvals }
      work rest snapshot fields (out ++ [msg])
    | .cancel timer =>
      work rest (cancelTimer snapshot timer) fields out
    | .arm timer delayExpr =>
      let d := eval snapshot fields delayExpr
      match armTimer snapshot timer d with
      | .ok snap' => work rest snap' fields out
      | .error f => .error f

def zeroValues : Values :=
  { integers := fun _ => 0, booleans := fun _ => false, texts := fun _ => "",
    buffers := fun _ => [], sequences := fun _ => ⟨0, by decide⟩ }

def invariantsHold (model : Model) (snapshot : Snapshot) : Bool :=
  model.invariants.all (fun inv => eval snapshot zeroValues inv)

def withoutFiring (snapshot : Snapshot) (firing : Option Nat) : Snapshot :=
  match firing with
  | some timer => cancelTimer snapshot timer
  | none => snapshot

def runRule (model : Model) (snapshot : Snapshot) (r : Rule) (fields : Values)
    (event : Nat) (firing : Option Nat) : Except Fault Transition :=
  match work r.actions (withoutFiring snapshot firing) fields [] with
  | .error f => .error f
  | .ok (snap, emitted) =>
    let after := { snap with state := r.target }
    if invariantsHold model after then
      .ok { after := after, rule := r.id, event := event, emitted := emitted }
    else .error .invariant

def enabled (model : Model) (snapshot : Snapshot) (event : Nat)
    (fields : Values) : List Rule :=
  model.rules.filter (fun r =>
    r.source == snapshot.state && r.event == event && eval snapshot fields r.guard)

def fire (model : Model) (snapshot : Snapshot) (event : Nat) (fields : Values)
    (firing : Option Nat) : Except Fault Transition :=
  match enabled model snapshot event fields with
  | [] => .error .uncovered
  | [r] => runRule model snapshot r fields event firing
  | _ => .error .conflict

def nextTimer (snapshot : Snapshot) : Option TimerEntry :=
  snapshot.timers.foldl (fun best entry =>
    match best with
    | none => some entry
    | some b => if entry.due < b.due ∨ (entry.due = b.due ∧ entry.timer < b.timer)
        then some entry else best) none

def stepTimer (model : Model) (snapshot : Snapshot) (time : Int) : Except Fault Transition :=
  if time < snapshot.now then .error .time
  else
    match nextTimer snapshot with
    | none => .error .noTimer
    | some entry =>
      if entry.due != time then .error .time
      else
        let event := model.timerEvents entry.timer
        fire model { snapshot with now := time } event zeroValues (some entry.timer)
def external (model : Model) (snapshot : Snapshot) (event : Nat) (fields : Values)
    (time : Int) : Except Fault Transition :=
  if time < snapshot.now then .error .time
  else if !(event ∈ model.externalEvents) then .error .timerInjection
  else if (match nextTimer snapshot with
          | some te => decide (te.due <= time)
          | none => false) then .error .pendingTimer
  else fire model { snapshot with now := time } event fields none

def rollback (initial : Snapshot) (result : Except Fault Transition) : Snapshot :=
  match result with
  | .ok t => t.after
  | .error _ => initial

theorem get_set_same (k : Kind) (slot : Nat) (v : Value k) (store : Values) :
  getValue k (setValue k slot v store) slot = v :=
by
  cases k <;> simp [setValue, getValue]

theorem rollback_error (initial : Snapshot) (f : Fault) :
  rollback initial (.error f) = initial :=
by
  simp [rollback]

theorem cancel_membership (snapshot : Snapshot) (timer : Nat) :
  ∀ te ∈ (cancelTimer snapshot timer).timers, te.timer ≠ timer :=
by
  intro te h
  simp [cancelTimer] at h
  exact h.2

theorem runRule_invariant (model : Model) (snapshot : Snapshot) (r : Rule)
    (fields : Values) (event : Nat) (firing : Option Nat) (t : Transition) :
    runRule model snapshot r fields event firing = .ok t →
    invariantsHold model t.after = true := by
  intro h
  unfold runRule at h
  split at h
  · contradiction
  · dsimp only at h
    split at h
    · cases h
      assumption
    · contradiction

theorem fire_invariant (model : Model) (snapshot : Snapshot) (event : Nat)
    (fields : Values) (firing : Option Nat) (t : Transition) :
    fire model snapshot event fields firing = .ok t →
    invariantsHold model t.after = true := by
  intro h
  unfold fire at h
  split at h
  · contradiction
  · exact runRule_invariant _ _ _ _ _ _ _ h
  · contradiction

end FormalSpecAgent.TypedMachine
