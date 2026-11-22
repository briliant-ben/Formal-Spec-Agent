import Approved

namespace TCPIPTimerCoverage
open Approved FormalSpecAgent TypedMachine TypedIR TimedSelection
set_option maxRecDepth 16384

private theorem invariant (s : Snapshot) (valid : invariantsHold model s = true)
    (expr : Expr .boolean) (member : expr ∈ model.invariants) : TypedMachine.eval s zeroValues expr = true :=
  List.all_eq_true.mp valid expr member

private def Covered (s : Snapshot) (id : Nat) : Prop :=
  ∃ r ∈ model.rules, r.source = s.state ∧ r.event = model.timerEvents id ∧
    TypedMachine.eval s zeroValues r.guard = true

private theorem choose (s : Snapshot) (state : s.state = 0) (id index : Nat) (r : Rule)
    (selected : model.rules[index]? = some r) (source : r.source = 0)
    (event : r.event = model.timerEvents id) (guard : TypedMachine.eval s zeroValues r.guard = true) :
    Covered s id :=
  ⟨r, List.mem_iff_getElem?.mpr ⟨index, selected⟩, source.trans state.symm, event, guard⟩

private theorem both (s : Snapshot) (left right : Expr .boolean)
    (a : TypedMachine.eval s zeroValues left = true) (b : TypedMachine.eval s zeroValues right = true) :
    TypedMachine.eval s zeroValues (.boolAnd left right) = true := by
  change (TypedMachine.eval s zeroValues left && TypedMachine.eval s zeroValues right) = true
  rw [a, b]
  rfl

private theorem arp_phase (s : Snapshot) (valid : invariantsHold model s = true) :
    TypedMachine.eval s zeroValues e16 = true ∨ TypedMachine.eval s zeroValues e35 = true ∨
      TypedMachine.eval s zeroValues e38 = true := by
  have phase := invariant s valid e1628 (by rw [model_invariants]; simp)
  change ((TypedMachine.eval s zeroValues e16 || TypedMachine.eval s zeroValues e35) ||
    TypedMachine.eval s zeroValues e38) = true at phase
  simpa only [Bool.or_eq_true, or_assoc] using phase

private theorem cache (s : Snapshot) (state : s.state = 0) (valid : invariantsHold model s = true)
    (active : TypedMachine.eval s zeroValues e1591 = true) : Covered s 0 := by
  rcases arp_phase s valid with empty | pending | resolved
  · have check := invariant s valid e1594 (by rw [model_invariants]; simp)
    change (!TypedMachine.eval s zeroValues e16 ||
      (TypedMachine.eval s zeroValues e1590 && !TypedMachine.eval s zeroValues e1591)) = true at check
    simp [empty, active] at check
  · have check := invariant s valid e1597 (by rw [model_invariants]; simp)
    change (!TypedMachine.eval s zeroValues e35 ||
      (TypedMachine.eval s zeroValues e1595 && !TypedMachine.eval s zeroValues e1591)) = true at check
    simp [pending, active] at check
  · exact choose s state 0 4 rule_4 rfl rfl rfl (both s e38 e3 resolved rfl)

private theorem query (s : Snapshot) (state : s.state = 0) (valid : invariantsHold model s = true)
    (active : TypedMachine.eval s zeroValues e1588 = true) : Covered s 1 := by
  have pending : TypedMachine.eval s zeroValues e35 = true := by
    rcases arp_phase s valid with empty | pending | resolved
    · have check := invariant s valid e1594 (by rw [model_invariants]; simp)
      change (!TypedMachine.eval s zeroValues e16 ||
        ((TypedMachine.eval s zeroValues e1587 && !TypedMachine.eval s zeroValues e1588) &&
          TypedMachine.eval s zeroValues e1592)) = true at check
      simp [empty, active] at check
    · exact pending
    · have check := invariant s valid e1601 (by rw [model_invariants]; simp)
      change (!TypedMachine.eval s zeroValues e38 ||
        ((TypedMachine.eval s zeroValues e1598 && !TypedMachine.eval s zeroValues e1588) &&
          TypedMachine.eval s zeroValues e1591)) = true at check
      simp [resolved, active] at check
  have retries := invariant s valid e1604 (by rw [model_invariants]; simp)
  change (decide (0 ≤ TypedMachine.eval s zeroValues e41) &&
    decide (TypedMachine.eval s zeroValues e41 ≤ 1)) = true at retries
  simp only [Bool.and_eq_true, decide_eq_true_eq] at retries
  by_cases first : TypedMachine.eval s zeroValues e41 = 0
  · exact choose s state 1 3 rule_3 rfl rfl rfl (both s e35 e42 pending (decide_eq_true first))
  have retry : TypedMachine.eval s zeroValues e198 = true := by
    change decide (TypedMachine.eval s zeroValues e41 = 1) = true
    have one (x : Int) (lo : 0 ≤ x) (hi : x ≤ 1) (nonzero : x ≠ 0) : x = 1 := by omega
    exact decide_eq_true (one _ retries.1 retries.2 first)
  have lengths := invariant s valid e1615 (by rw [model_invariants]; simp)
  change (TypedMachine.eval s zeroValues e211 || TypedMachine.eval s zeroValues e201) = true at lengths
  rcases Bool.or_eq_true_iff.mp lengths with empty | nonempty
  · exact choose s state 1 26 rule_26 rfl rfl rfl (both s e35 e212 pending (both s e198 e211 retry empty))
  · have kind := invariant s valid e1721 (by rw [model_invariants]; simp)
    change ((TypedMachine.eval s zeroValues e1717 || (TypedMachine.eval s zeroValues e205 ||
      TypedMachine.eval s zeroValues e209)) &&
      decide (TypedMachine.eval s zeroValues e1717 = TypedMachine.eval s zeroValues e211)) = true at kind
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at kind
    have noEmpty : TypedMachine.eval s zeroValues e211 = false := by
      have len : 28 ≤ TypedMachine.eval s zeroValues e200 := of_decide_eq_true nonempty
      change decide (TypedMachine.eval s zeroValues e200 = 0) = false
      have nonzero (x : Int) (low : 28 ≤ x) : x ≠ 0 := by omega
      exact decide_eq_false (nonzero _ len)
    rw [noEmpty] at kind
    have resolvedGuard : TypedMachine.eval s zeroValues e203 = true :=
      both s e35 e202 pending (both s e198 e201 retry nonempty)
    rcases kind.1 with ownerNone | udp | tcp
    · simp [ownerNone] at kind
    · exact choose s state 1 24 rule_24 rfl rfl rfl (both s e203 e205 resolvedGuard udp)
    · exact choose s state 1 25 rule_25 rfl rfl rfl (both s e203 e209 resolvedGuard tcp)

private theorem tcp_phase (s : Snapshot) (valid : invariantsHold model s = true) :
    TypedMachine.eval s zeroValues e489 = true ∨
      TypedMachine.eval s zeroValues e580 = true ∨
      TypedMachine.eval s zeroValues e743 = true ∨
      TypedMachine.eval s zeroValues e810 = true ∨
      TypedMachine.eval s zeroValues e923 = true ∨
      TypedMachine.eval s zeroValues e955 = true ∨
      TypedMachine.eval s zeroValues e959 = true ∨
      TypedMachine.eval s zeroValues e944 = true ∨
      TypedMachine.eval s zeroValues e962 = true ∨
      TypedMachine.eval s zeroValues e964 = true ∨
      TypedMachine.eval s zeroValues e967 = true := by
  have phase := invariant s valid e1716 (by rw [model_invariants]; simp)
  change ((((((((((TypedMachine.eval s zeroValues e489 ||
      TypedMachine.eval s zeroValues e580) ||
      TypedMachine.eval s zeroValues e743) ||
      TypedMachine.eval s zeroValues e810) ||
      TypedMachine.eval s zeroValues e923) ||
      TypedMachine.eval s zeroValues e955) ||
      TypedMachine.eval s zeroValues e959) ||
      TypedMachine.eval s zeroValues e944) ||
      TypedMachine.eval s zeroValues e962) ||
      TypedMachine.eval s zeroValues e964) ||
      TypedMachine.eval s zeroValues e967) = true at phase
  simpa only [Bool.or_eq_true, or_assoc] using phase

private theorem blocked (s : Snapshot) (valid : invariantsHold model s = true)
    (phase timer : Expr .boolean)
    (member : .implies phase (.equal .boolean timer e4) ∈ model.invariants)
    (on : TypedMachine.eval s zeroValues phase = true)
    (active : TypedMachine.eval s zeroValues timer = true) : False := by
  have inv := invariant s valid _ member
  change (!TypedMachine.eval s zeroValues phase || decide (TypedMachine.eval s zeroValues timer = false)) = true at inv
  simp [on, active] at inv

private theorem rtx_for_link (s : Snapshot) (state : s.state = 0) (valid : invariantsHold model s = true)
    (guard : Expr .boolean) (enabled : TypedMachine.eval s zeroValues guard = true)
    (empty pending resolved : Rule) (emptyIdx pendingIdx resolvedIdx : Nat)
    (emptyRule : model.rules[emptyIdx]? = some empty)
    (pendingRule : model.rules[pendingIdx]? = some pending)
    (resolvedRule : model.rules[resolvedIdx]? = some resolved)
    (emptyShape : empty.source = 0 ∧ empty.event = model.timerEvents 2 ∧ empty.guard = .boolAnd guard e16)
    (pendingShape : pending.source = 0 ∧ pending.event = model.timerEvents 2 ∧ pending.guard = .boolAnd guard e35)
    (resolvedShape : resolved.source = 0 ∧ resolved.event = model.timerEvents 2 ∧ resolved.guard = .boolAnd guard e38) :
    Covered s 2 := by
  rcases arp_phase s valid with noCache | querySent | hasCache
  · exact choose s state 2 emptyIdx empty emptyRule emptyShape.1 emptyShape.2.1
      (emptyShape.2.2 ▸ both s guard e16 enabled noCache)
  · exact choose s state 2 pendingIdx pending pendingRule pendingShape.1 pendingShape.2.1
      (pendingShape.2.2 ▸ both s guard e35 enabled querySent)
  · exact choose s state 2 resolvedIdx resolved resolvedRule resolvedShape.1 resolvedShape.2.1
      (resolvedShape.2.2 ▸ both s guard e38 enabled hasCache)

private theorem retransmit (s : Snapshot) (state : s.state = 0) (valid : invariantsHold model s = true)
    (active : TypedMachine.eval s zeroValues e1629 = true) : Covered s 2 := by
  rcases tcp_phase s valid with closed | listen | synSent | synReceived | established | finWait1 | closeWait | finWait2 | closing | lastAck | timeWait
  · exact (blocked s valid e489 e1629 (show e1631 ∈ model.invariants from by rw [model_invariants]; simp) closed active).elim
  · exact (blocked s valid e580 e1629 (show e1638 ∈ model.invariants from by rw [model_invariants]; simp) listen active).elim
  · exact rtx_for_link s state valid e954 (both s e743 e3 synSent rfl)
      rule_150 rule_151 rule_152 150 151 152 rfl rfl rfl
      ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩
  · exact rtx_for_link s state valid e1048 (both s e810 e3 synReceived rfl)
      rule_153 rule_154 rule_155 153 154 155 rfl rfl rfl
      ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩
  · have activity := invariant s valid e1687 (by rw [model_invariants]; simp)
    change (!TypedMachine.eval s zeroValues e923 ||
      decide (TypedMachine.eval s zeroValues e1629 = TypedMachine.eval s zeroValues e1243)) = true at activity
    simp only [established, active, Bool.not_true, Bool.false_or, decide_eq_true_eq] at activity
    exact rtx_for_link s state valid e1328 (both s e923 e1243 established activity.symm)
      rule_258 rule_259 rule_260 258 259 260 rfl rfl rfl ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩
  · exact rtx_for_link s state valid e956 (both s e955 e3 finWait1 rfl)
      rule_156 rule_157 rule_158 156 157 158 rfl rfl rfl
      ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩
  · exact (blocked s valid e959 e1629 (show e1654 ∈ model.invariants from by rw [model_invariants]; simp) closeWait active).elim
  · exact (blocked s valid e944 e1629 (show e1657 ∈ model.invariants from by rw [model_invariants]; simp) finWait2 active).elim
  · exact rtx_for_link s state valid e963 (both s e962 e3 closing rfl)
      rule_159 rule_160 rule_161 159 160 161 rfl rfl rfl
      ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩
  · exact rtx_for_link s state valid e965 (both s e964 e3 lastAck rfl)
      rule_162 rule_163 rule_164 162 163 164 rfl rfl rfl
      ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩
  · exact (blocked s valid e967 e1629 (show e1666 ∈ model.invariants from by rw [model_invariants]; simp) timeWait active).elim

private theorem time_wait (s : Snapshot) (state : s.state = 0) (valid : invariantsHold model s = true)
    (active : TypedMachine.eval s zeroValues e1635 = true) : Covered s 3 := by
  rcases tcp_phase s valid with closed | listen | synSent | synReceived | established | finWait1 | closeWait | finWait2 | closing | lastAck | timeWait
  · exact (blocked s valid e489 e1635 (show e1637 ∈ model.invariants from by rw [model_invariants]; simp) closed active).elim
  · exact (blocked s valid e580 e1635 (show e1640 ∈ model.invariants from by rw [model_invariants]; simp) listen active).elim
  · exact (blocked s valid e743 e1635 (show e1645 ∈ model.invariants from by rw [model_invariants]; simp) synSent active).elim
  · exact (blocked s valid e810 e1635 (show e1648 ∈ model.invariants from by rw [model_invariants]; simp) synReceived active).elim
  · exact (blocked s valid e923 e1635 (show e1650 ∈ model.invariants from by rw [model_invariants]; simp) established active).elim
  · exact (blocked s valid e955 e1635 (show e1653 ∈ model.invariants from by rw [model_invariants]; simp) finWait1 active).elim
  · exact (blocked s valid e959 e1635 (show e1656 ∈ model.invariants from by rw [model_invariants]; simp) closeWait active).elim
  · exact (blocked s valid e944 e1635 (show e1659 ∈ model.invariants from by rw [model_invariants]; simp) finWait2 active).elim
  · exact (blocked s valid e962 e1635 (show e1662 ∈ model.invariants from by rw [model_invariants]; simp) closing active).elim
  · exact (blocked s valid e964 e1635 (show e1665 ∈ model.invariants from by rw [model_invariants]; simp) lastAck active).elim
  · exact choose s state 3 171 rule_171 rfl rfl rfl (both s e967 e3 timeWait rfl)

private theorem user_timeout (s : Snapshot) (state : s.state = 0) (valid : invariantsHold model s = true)
    (active : TypedMachine.eval s zeroValues e1632 = true) : Covered s 4 := by
  rcases tcp_phase s valid with closed | listen | synSent | synReceived | established | finWait1 | closeWait | finWait2 | closing | lastAck | timeWait
  · exact (blocked s valid e489 e1632 (show e1634 ∈ model.invariants from by rw [model_invariants]; simp) closed active).elim
  · exact (blocked s valid e580 e1632 (show e1639 ∈ model.invariants from by rw [model_invariants]; simp) listen active).elim
  · exact choose s state 4 165 rule_165 rfl rfl rfl (both s e743 e3 synSent rfl)
  · exact choose s state 4 166 rule_166 rfl rfl rfl (both s e810 e3 synReceived rfl)
  · exact (blocked s valid e923 e1632 (show e1649 ∈ model.invariants from by rw [model_invariants]; simp) established active).elim
  · exact choose s state 4 167 rule_167 rfl rfl rfl (both s e955 e3 finWait1 rfl)
  · exact choose s state 4 168 rule_168 rfl rfl rfl (both s e959 e3 closeWait rfl)
  · exact (blocked s valid e944 e1632 (show e1658 ∈ model.invariants from by rw [model_invariants]; simp) finWait2 active).elim
  · exact choose s state 4 169 rule_169 rfl rfl rfl (both s e962 e3 closing rfl)
  · exact choose s state 4 170 rule_170 rfl rfl rfl (both s e964 e3 lastAck rfl)
  · exact (blocked s valid e967 e1632 (show e1667 ∈ model.invariants from by rw [model_invariants]; simp) timeWait active).elim
theorem covered : CoversTimers model declaredStates declaredTimers := by
  intro s member valid entry inside known
  have state : s.state = 0 := List.mem_singleton.mp member
  have active : TypedMachine.eval s zeroValues (.timerActive entry.timer) = true := by
    change decide (entry.timer ∈ s.timers.map TimerEntry.timer) = true
    exact decide_eq_true (List.mem_map.mpr ⟨entry, inside, rfl⟩)
  simp only [declaredTimers, List.mem_cons, List.not_mem_nil, or_false] at known
  rcases known with id | id | id | id | id <;> rw [id] at active ⊢
  · exact cache s state valid active
  · exact query s state valid active
  · exact retransmit s state valid active
  · exact time_wait s state valid active
  · exact user_timeout s state valid active

end TCPIPTimerCoverage
