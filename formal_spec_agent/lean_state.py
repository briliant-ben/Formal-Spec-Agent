"""Frozen integer action-block contracts, not whole EFSM or native C proofs."""
import hashlib
import json
import re
from pathlib import Path

from protocol_lab.ir import load, model_files
from . import lean_backend as gate

HERE = Path(__file__).resolve().parent
NS = 'FormalSpecAgent.StateSubset.'
SCOPE = ('Selected integer-only, timer-free IR action block: ordered updates, '
         'buffered emissions and final-invariant rollback. Not guard selection, '
         'scheduling, native overflow, parsed C correspondence or whole protocol.')


def integer(e, variables, fields, *, invariant=False):
    if type(e) is int:
        if not -(2**63) <= e < 2**63:
            raise ValueError('State unit literal outside signed64')
        return '(' + NS + 'IntegerExpr.literal ' + gate.number(e) + ')'
    if type(e) is not dict or len(e) != 1:
        raise ValueError('Unsupported state integer expression')
    if set(e) == {'var'} and e['var'] in variables:
        return '(' + NS + 'IntegerExpr.variable ' + str(variables.index(e['var'])) + ')'
    if not invariant and set(e) == {'event'} and e['event'] in fields:
        return '(' + NS + 'IntegerExpr.field ' + str(fields.index(e['event'])) + ')'
    raise ValueError('Unsupported state expression or invariant event field')


def predicate(p, variables):
    if type(p) is bool:
        return '(' + NS + 'Predicate.literal ' + str(p).lower() + ')'
    if type(p) is not dict or set(p) != {'op', 'args'} or type(p['args']) is not list or len(p['args']) != 2:
        raise ValueError('Unsupported state invariant predicate')
    op = p['op']; a, b = p['args']
    if op == 'and':
        return '(' + NS + 'Predicate.conjunction ' + predicate(a, variables) + ' ' + predicate(b, variables) + ')'
    if op not in ('eq', 'le', 'ge'):
        raise ValueError('Unsupported state invariant operator')
    if op == 'ge': a, b = b, a
    return '(' + NS + ('Predicate.equal ' if op == 'eq' else 'Predicate.lessEqual ') + integer(a, variables, [], invariant=True) + ' ' + integer(b, variables, [], invariant=True) + ')'


def ints(values):
    if type(values) is not list or not values or len(values) > 64 or any(type(n) is not int or not -(2**63) <= n < 2**63 for n in values):
        raise ValueError('State witness requires bounded signed64 integer list')
    return '[' + ', '.join(gate.number(n) for n in values) + ']'


def prepare(task_file, workspace, task_sha256, *, draft=False):
    root = Path(workspace).resolve(); task_file = Path(task_file).resolve()
    if not task_file.is_relative_to(root) or gate.sha(task_file) != task_sha256:
        raise ValueError('State task outside workspace or digest mismatch')
    t = json.loads(task_file.read_text())
    keys = {'schema', 'id', 'model', 'model_sha256', 'sources', 'target', 'witnesses', 'lean_version', 'foundation_sha256', 'state_semantics_sha256', 'adapter_sha256', 'approved_sha256'}
    if set(t) != keys or t['schema'] != 'fsa-lean-state-task-v1' or t['lean_version'] != gate.VERSION:
        raise ValueError('Unsupported state task schema/version')
    if type(t['id']) is not str or not re.fullmatch(r'[A-Za-z0-9_-]{1,80}', t['id']):
        raise ValueError('Invalid state task identity')
    for p, h in [(HERE/'lean/Foundation.lean', t['foundation_sha256']), (HERE/'lean/StateSubset.lean', t['state_semantics_sha256']), (Path(__file__).resolve(), t['adapter_sha256'])]:
        if gate.sha(p) != h: raise ValueError('State semantic/adapter approval epoch changed')
    model_file = gate.inside(root, t['model']); chain = model_files(model_file)
    if gate.sha(model_file) != t['model_sha256']: raise ValueError('State model digest mismatch')
    paths = [task_file, *chain]; pinned = set()
    if type(t['sources']) is not list or not t['sources']: raise ValueError('State sources required')
    for row in t['sources']:
        if set(row) != {'path', 'sha256'}: raise ValueError('Bad state source binding')
        p = gate.inside(root, row['path'])
        if gate.sha(p) != row['sha256']: raise ValueError('State source digest mismatch')
        paths.append(p); pinned.add(p)
    if not set(chain[1:]) <= pinned: raise ValueError('Every model base must be pinned')
    m = load(model_file)
    if m['ir_version'] not in ('0.5', '0.6') or m['semantics'] != 'flat-efsm-atomic-ordered-v1' or m['timers'] or len(m['states']) != 1:
        raise ValueError('State unit requires single-state atomic-v1 without timers')
    variables = list(m['variables'])
    if not 1 <= len(variables) <= 64 or any(v['type'] != 'int' for v in m['variables'].values()):
        raise ValueError('State unit requires integer variables only')
    rules = [r for r in m['transitions'] if r['id'] == t['target']]
    if len(rules) != 1: raise ValueError('Unknown state target rule')
    r = rules[0]; fields = list(m['events'][r['event']]['fields'])
    if r['guard'] is not True or r.get('target_cases') or r['from'] != r['to'] or m['events'][r['event']]['origin'] != 'application':
        raise ValueError('State action unit excludes selection, target cases and non-application events')
    if not 1 <= len(fields) <= 64 or any(k != 'int' for k in m['events'][r['event']]['fields'].values()):
        raise ValueError('State unit requires integer event fields')
    if not 1 <= len(r['actions']) <= 64: raise ValueError('State action count outside profile')
    messages = list(m['messages']); actions = []
    for a in r['actions']:
        if set(a) == {'set'}:
            s = a['set']
            if set(s) != {'var', 'value'}: raise ValueError('Bad state assignment')
            actions.append('(' + NS + 'Action.assign ' + str(variables.index(s['var'])) + ' ' + integer(s['value'], variables, fields) + ')')
        elif set(a) == {'emit'}:
            s = a['emit']; schema = m['messages'][s['message']]['fields']
            if set(s) != {'message', 'fields'} or len(schema) != 1 or list(schema.values()) != ['int']:
                raise ValueError('State emissions require one integer field')
            actions.append('(' + NS + 'Action.emit ' + str(messages.index(s['message'])) + ' ' + integer(next(iter(s['fields'].values())), variables, fields) + ')')
        else: raise ValueError('Unsupported state action')
    if not m['invariants']: raise ValueError('Nonempty state invariant contract required')
    inv = '[' + ', '.join(predicate(i['assert'], variables) for i in m['invariants']) + ']'
    source = 'import StateSubset\n\nnamespace Approved\n\ndef actions : List ' + NS + 'Action :=\n  [' + ', '.join(actions) + ']\n\ndef invariants : List ' + NS + 'Predicate :=\n  ' + inv + '\n\n'
    goals = {
        'failure_rolls_back': '∀ (actions : List ' + NS + 'Action) (invariants : List ' + NS + 'Predicate) (s env : List Int), (' + NS + 'execute actions invariants s env).accepted = false → ' + NS + 'execute actions invariants s env = ⟨false, s, []⟩',
        'success_checks_invariants': '∀ (actions : List ' + NS + 'Action) (invariants : List ' + NS + 'Predicate) (s env : List Int), (' + NS + 'execute actions invariants s env).accepted = true → ' + NS + 'invariantsHold invariants (' + NS + 'execute actions invariants s env).values = true',
        'assignment_then_emission': '∀ (s env : List Int) (n : Nat) (value : Int), n < s.length → ' + NS + 'work [' + NS + 'Action.assign n (' + NS + 'IntegerExpr.literal value), ' + NS + 'Action.emit 0 (' + NS + 'IntegerExpr.variable n)] s env [] = (s.set n value, [(0, value)])',
    }
    ws = t['witnesses']
    if type(ws) is not list or not 2 <= len(ws) <= 32: raise ValueError('Positive and negative state witnesses required')
    successes = failures = False
    for w in ws:
        if set(w) != {'id', 'initial', 'fields', 'accepted', 'values', 'emitted'} or type(w['id']) is not str or not re.fullmatch(r'[a-z][a-z0-9_]{0,50}', w['id']):
            raise ValueError('Bad state witness')
        name = 'witness_' + w['id']
        if name in goals or name + '_admitted' in goals or type(w['accepted']) is not bool or any(type(w[k]) is not list for k in ['initial', 'values', 'fields']):
            raise ValueError('Bad state witness dimensions/identity')
        if len(w['initial']) != len(variables) or len(w['values']) != len(variables) or len(w['fields']) != len(fields):
            raise ValueError('Bad state witness dimensions/identity')
        initial, env, expected = ints(w['initial']), ints(w['fields']), ints(w['values'])
        if type(w['emitted']) is not list or len(w['emitted']) > 64: raise ValueError('Bad state witness output')
        output = []
        for row in w['emitted']:
            if type(row) is not list or len(row) != 2 or type(row[0]) is not int or not 0 <= row[0] < len(messages): raise ValueError('Bad state emitted message')
            ints([row[1]]); output.append('(' + str(row[0]) + ', ' + gate.number(row[1]) + ')')
        goals[name] = NS + 'execute actions invariants ' + initial + ' ' + env + ' = ⟨' + str(w['accepted']).lower() + ', ' + expected + ', [' + ', '.join(output) + ']⟩'
        goals[name + '_admitted'] = NS + 'invariantsHold invariants ' + initial + ' = true'
        successes |= w['accepted']; failures |= not w['accepted']
    if not (successes and failures): raise ValueError('Both successful and rejected witnesses required')
    source += '\n\n'.join('def ' + k + ' : Prop :=\n  ' + v for k, v in goals.items()) + '\n\nend Approved\n'
    if not draft and hashlib.sha256(source.encode()).hexdigest() != t['approved_sha256']: raise ValueError('State statement approval mismatch')
    inputs = {'workspace/' + str(p.relative_to(root)): gate.sha(p) for p in paths}
    for p in [Path(__file__).resolve(), HERE/'lean_backend.py', HERE/'lean/Foundation.lean', HERE/'lean/StateSubset.lean', HERE/'lean/lean-toolchain']:
        inputs['tool/' + str(p.relative_to(HERE))] = gate.sha(p)
    inputs['ir_checker'] = gate.sha(HERE.parent/'protocol_lab/ir.py')
    return source, list(goals), inputs
