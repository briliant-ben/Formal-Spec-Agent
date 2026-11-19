import BatchTotality

namespace FormalSpecAgent.TimedObligations

open TypedMachine TypedIR TypedFiringContracts TypedContracts

/-- Every raw firing of a matching rule, including each possible timer identity. -/
def rawChecks (model : Model) (ids : List Nat) : List (Rule × Option Nat) :=
  model.rules.flatMap fun rule =>
    (if rule.event ∈ model.externalEvents then [(rule, none)] else []) ++
    ids.filterMap fun id =>
      if rule.event = model.timerEvents id then some (rule, some id) else none

theorem raw_external_member (model : Model) (ids : List Nat) (rule : Rule)
    (member : rule ∈ model.rules) (external : rule.event ∈ model.externalEvents) :
    (rule, none) ∈ rawChecks model ids := by
  apply List.mem_flatMap.mpr
  exact ⟨rule, member, List.mem_append.mpr (Or.inl (by simp [external]))⟩

theorem raw_timer_member (model : Model) (ids : List Nat) (rule : Rule) (timer : Nat)
    (member : rule ∈ model.rules) (declared : timer ∈ ids)
    (trigger : rule.event = model.timerEvents timer) :
    (rule, some timer) ∈ rawChecks model ids := by
  apply List.mem_flatMap.mpr
  refine ⟨rule, member, List.mem_append.mpr (Or.inr ?_)⟩
  exact List.mem_filterMap.mpr ⟨timer, declared, by simp [trigger]⟩

def ruleKey (r : Rule) : Nat × Nat := (r.source, r.event)

/-- Only distinct IDs sharing a source and an event can conflict. Each such
group gets one obligation, even when it contains many potential pairs. -/
def conflictChecks (model : Model) : List (List Rule) :=
  ((model.rules.map ruleKey).eraseDups).map fun key =>
    model.rules.filter fun rule => ruleKey rule == key

def ConflictFree (model : Model) (rules : List Rule) : Prop :=
  ∀ (snapshot : Snapshot) (fields : Values),
    invariantsHold model snapshot = true →
    ∀ left ∈ rules, ∀ right ∈ rules,
      left.id ≠ right.id →
      left.source = snapshot.state →
      eval snapshot fields left.guard = false ∨ eval snapshot fields right.guard = false

/-- A finite list of individually named semantic obligations can be assembled
without searching for a concrete snapshot or placing a bound on the input. -/
def Each (property : α → Prop) : List α → Prop
  | [] => True
  | first :: rest => property first ∧ Each property rest

theorem Each.of_mem {property : α → Prop} {items : List α} {item : α}
    (checked : Each property items) (member : item ∈ items) : property item := by
  induction items with
  | nil => simp at member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with equal | member
    · exact equal ▸ checked.1
    · exact ih checked.2 member

theorem external_raw_from_checks (model : Model) (ids : List Nat)
    (checked : Each (fun p => FiringPreserves model p.1 p.2) (rawChecks model ids)) :
    ∀ event ∈ model.externalEvents, ScheduledPreservation.MatchingRaw model event none := by
  intro event allowed rule member trigger
  apply checked.of_mem (item := (rule, none))
  exact raw_external_member model ids rule member (trigger.symm ▸ allowed)

theorem timer_raw_from_checks (model : Model) (ids : List Nat)
    (checked : Each (fun p => FiringPreserves model p.1 p.2) (rawChecks model ids)) :
    BatchPreservation.TimerRaw ids model := by
  intro timer known rule member trigger
  apply checked.of_mem (item := (rule, some timer))
  exact raw_timer_member model ids rule timer member known trigger

theorem disjoint_from_checks (model : Model)
    (checked : Each (ConflictFree model) (conflictChecks model)) :
    GuardsDisjoint model := by
  intro snapshot fields valid event left right leftMember rightMember distinct leftSource
    rightSource leftEvent rightEvent
  let key := ruleKey left
  let group := model.rules.filter fun rule => ruleKey rule == key
  have sameKey : ruleKey right = key :=
    Prod.ext (rightSource.trans leftSource.symm) (rightEvent.trans leftEvent.symm)
  have leftIn : left ∈ group := List.mem_filter.mpr ⟨leftMember, by simp [key]⟩
  have rightIn : right ∈ group := List.mem_filter.mpr ⟨rightMember, by simp [sameKey]⟩
  have groupIn : group ∈ conflictChecks model := List.mem_map.mpr
    ⟨key, List.mem_eraseDups.mpr (List.mem_map.mpr ⟨left, leftMember, rfl⟩), rfl⟩
  exact checked.of_mem groupIn snapshot fields valid left leftIn right rightIn distinct leftSource

theorem timer_contracts_from_checks (model : Model) (states ids : List Nat)
    (targets : BatchTotality.TargetsDeclared model states)
    (arms : TimerDomain.ArmsDeclared ids model)
    (unique : (model.rules.map Rule.id).Nodup)
    (timers : TimedSelection.CoversTimers model states ids)
    (raw : Each (fun p => FiringPreserves model p.1 p.2) (rawChecks model ids))
    (conflicts : Each (ConflictFree model) (conflictChecks model)) :
    BatchTotality.TimerContracts model states ids :=
  ⟨targets, arms, unique, disjoint_from_checks model conflicts, timers,
    timer_raw_from_checks model ids raw⟩

theorem contracts_from_checks (model : Model) (states ids : List Nat)
    (targets : BatchTotality.TargetsDeclared model states)
    (arms : TimerDomain.ArmsDeclared ids model)
    (unique : (model.rules.map Rule.id).Nodup)
    (timers : TimedSelection.CoversTimers model states ids)
    (external : Covers model states)
    (raw : Each (fun p => FiringPreserves model p.1 p.2) (rawChecks model ids))
    (conflicts : Each (ConflictFree model) (conflictChecks model)) :
    BatchTotality.Contracts model states ids :=
  let base := timer_contracts_from_checks model states ids targets arms unique timers raw conflicts
  ⟨base.targets, base.arms, base.unique, base.disjoint, base.timerCoverage, base.timerRaw,
    external, external_raw_from_checks model ids raw⟩

end FormalSpecAgent.TimedObligations
