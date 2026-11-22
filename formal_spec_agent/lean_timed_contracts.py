"""Derive named scheduler obligations from the authoritative typed IR."""
from collections import defaultdict

from .lean_batch import BatchView

TM = 'FormalSpecAgent.TypedMachine.'
TOTAL = 'FormalSpecAgent.BatchTotality.'
OBLIGATIONS = 'FormalSpecAgent.TimedObligations.'
FIRING = 'FormalSpecAgent.TypedFiringContracts.'


def entries(view):
    """Return the expected Lean catalogs in the same order as the model."""
    timers = defaultdict(list)
    for index, name in enumerate(view.timers):
        timers[view.m['timers'][name]['event']].append(index)

    rules = view.m['transitions']
    groups = defaultdict(list)
    for index, rule in enumerate(rules):
        groups[rule['from'], rule['event']].append(index)

    raw = []
    for index, rule in enumerate(rules):
        event = rule['event']
        if view.m['events'][event]['origin'] != 'timer':
            raw.append((index, None))
        raw.extend((index, timer) for timer in timers[event])
    return raw, list(groups.values())


def render(model):
    """Render open propositions. A source catalog alone discharges no claim."""
    if model.get('clocks') or model['scope'].get('terminal_states'):
        raise ValueError('Timed contracts require the atomic-v1 scheduler without clocks or terminal states')

    view = BatchView(model)
    source = view.source(proof_helpers=True).replace(
        'import BatchObserve\n', 'import BatchObserve\nimport TimedObligations\n', 1)
    initial = dict(state=model['initial_state'], now_ms=0,
                   variables={name: var['initial'] for name, var in model['variables'].items()},
                   timers={})
    states = list(range(len(view.v.states)))
    ids = list(range(len(view.timers)))
    raw, conflicts = entries(view)

    source += f'''
def initial : {TM}Snapshot := {view.snapshot(initial)}
def declaredStates : List Nat := {states}
def declaredTimers : List Nat := {ids}
'''

    goals = {
        'initial_admitted': f'{TOTAL}Admitted model declaredStates declaredTimers initial',
        'targets_declared': f'{TOTAL}TargetsDeclared model declaredStates',
        'arms_declared': 'FormalSpecAgent.TimerDomain.ArmsDeclared declaredTimers model',
        'rule_ids_unique': f'(model.rules.map {TM}Rule.id).Nodup',
        'timer_coverage': 'FormalSpecAgent.TimedSelection.CoversTimers model declaredStates declaredTimers',
        'external_coverage': 'FormalSpecAgent.TypedContracts.Covers model declaredStates',
    }

    raw_terms = []
    for index, timer in raw:
        firing = 'none' if timer is None else f'(some {timer})'
        suffix = 'external' if timer is None else f'timer_{timer}'
        rule = f'rule_{index}'
        raw_terms.append(f'({rule}, {firing})')
        goals[f'raw_{index}_{suffix}'] = f'{FIRING}FiringPreserves model {rule} {firing}'

    conflict_terms = []
    for index, group in enumerate(conflicts):
        terms = ', '.join(f'rule_{rule}' for rule in group)
        name = f'conflictGroup_{index}'
        source += f'\ndef {name} : List {TM}Rule := [{terms}]\n'
        conflict_terms.append(name)
        goals[f'conflict_{index}'] = f'{OBLIGATIONS}ConflictFree model {name}'

    source += f'\ndef rawCatalog : List ({TM}Rule × Option Nat) := [{", ".join(raw_terms)}]\n'
    source += f'\ndef conflictCatalog : List (List {TM}Rule) := [{", ".join(conflict_terms)}]\n'
    goals['raw_catalog_exact'] = f'{OBLIGATIONS}rawChecks model declaredTimers = rawCatalog'
    goals['conflict_catalog_exact'] = f'{OBLIGATIONS}conflictChecks model = conflictCatalog'
    source += '\n'.join(f'def {name} : Prop := {prop}' for name, prop in goals.items())
    return source + '\n\nend Approved\n', goals
