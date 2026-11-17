import BatchMachine

namespace FormalSpecAgent.BatchReplay
open TypedMachine TimerRank BatchMachine

/-- A timer prefix is prepended only if the entire suffix succeeds. -/
def prepend (transition : Transition) (rest : Except Fault Batch) : Except Fault Batch :=
  match rest with
  | .error fault => .error fault
  | .ok batch => .ok { after := batch.after, trace := transition :: batch.trace }

/-- Proof-carrying decomposition of the actual timer computation. Every leaf
    requires an equation about the real selector or stepper, never an assumed
    poststate. There is no fuel bound or additional protocol decision here. -/
inductive Replay (model : Model) (limit : Int) : Snapshot → Except Fault Batch → Prop where
  | empty (s : Snapshot) (hn : nextTimer s = none) :
      Replay model limit s (.ok { after := { s with now := limit }, trace := [] })
  | future (s : Snapshot) (entry : TimerEntry) (hn : nextTimer s = some entry)
      (hd : ¬entry.due ≤ limit) :
      Replay model limit s (.ok { after := { s with now := limit }, trace := [] })
  | failure (s : Snapshot) (entry : TimerEntry) (fault : Fault)
      (hn : nextTimer s = some entry) (hd : entry.due ≤ limit)
      (hs : stepTimer model s entry.due = .error fault) :
      Replay model limit s (.error fault)
  | step (s : Snapshot) (entry : TimerEntry) (transition : Transition)
      (rest : Except Fault Batch) (hn : nextTimer s = some entry)
      (hd : entry.due ≤ limit) (hs : stepTimer model s entry.due = .ok transition)
      (tail : Replay model limit transition.after rest) :
      Replay model limit s (prepend transition rest)

/-- Checked local replay facts imply equality with the total well-founded
    scheduler. This is a proof bridge, not an alternate runtime scheduler. -/
theorem sound {model : Model} {limit : Int} {s : Snapshot}
    {result : Except Fault Batch} (certificate : Replay model limit s result)
    (hwell : WellTimed s) (hbound : s.now ≤ limit) :
    advanceAux model s limit hwell hbound = result := by
  induction certificate with
  | empty s hn =>
      rw [advanceAux.eq_def]
      split <;> simp_all
  | future s entry hn hd =>
      rw [advanceAux.eq_def]
      split <;> simp_all
      subst_vars
      intro impossible
      omega
  | failure s entry fault hn hd hs =>
      rw [advanceAux.eq_def]
      split <;> simp_all
      subst_vars
      split <;> simp_all
  | step s entry transition rest hn hd hs tail ih =>
      rw [advanceAux.eq_def]
      split <;> simp_all [prepend]
      subst_vars
      split <;> simp_all
      subst_vars
      rfl

/-- The public entry point uses the same certified scheduler result. -/
theorem advance_result {model : Model} {limit : Int} {s : Snapshot}
    {result : Except Fault Batch} (certificate : Replay model limit s result)
    (hwell : WellTimed s) (hbound : s.now ≤ limit) :
    advance model s limit = result := by
  unfold advance
  have notPast : ¬limit < s.now := by omega
  simp only [dite_eq_right notPast, dite_eq_left hwell]
  exact sound certificate hwell hbound

/-- A failed timer suffix discards all earlier successful timer transitions. -/
theorem tick_failure {model : Model} {limit : Int} {s : Snapshot} {fault : Fault}
    (certificate : Replay model limit s (.error fault))
    (hwell : WellTimed s) (hbound : s.now ≤ limit) :
    tick model s limit = .error fault := by
  unfold tick
  rw [advance_result certificate hwell hbound]

/-- The final invariant check remains an explicit certificate obligation. -/
theorem tick_success {model : Model} {limit : Int} {s : Snapshot} {batch : Batch}
    (certificate : Replay model limit s (.ok batch))
    (hwell : WellTimed s) (hbound : s.now ≤ limit)
    (hinvariant : invariantsHold model batch.after = true) :
    tick model s limit = .ok batch := by
  unfold tick
  rw [advance_result certificate hwell hbound]
  simp only [hinvariant, ↓reduceIte]

theorem dispatch_timer_failure {model : Model} {limit : Int} {s : Snapshot}
    {fault : Fault} {event : Nat} {fields : TypedIR.Values}
    (hexternal : event ∈ model.externalEvents)
    (certificate : Replay model limit s (.error fault))
    (hwell : WellTimed s) (hbound : s.now ≤ limit) :
    dispatch model s event fields limit = .error fault := by
  unfold dispatch
  simp only [hexternal, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [advance_result certificate hwell hbound]

theorem dispatch_after_timers {model : Model} {limit : Int} {s : Snapshot}
    {batch : Batch} {event : Nat} {fields : TypedIR.Values} {transition : Transition}
    (hexternal : event ∈ model.externalEvents)
    (certificate : Replay model limit s (.ok batch))
    (hwell : WellTimed s) (hbound : s.now ≤ limit)
    (hexecute : external model batch.after event fields batch.after.now = .ok transition) :
    dispatch model s event fields limit =
      .ok { after := transition.after, trace := batch.trace ++ [transition] } := by
  unfold dispatch
  simp only [hexternal, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [advance_result certificate hwell hbound]
  simp only [hexecute]

theorem prefix_failure_rolls_back (s : Snapshot) (transition : Transition) (fault : Fault) :
    BatchMachine.rollback s (prepend transition (.error fault)) = s := by
  unfold BatchMachine.rollback prepend
  rfl

end FormalSpecAgent.BatchReplay
