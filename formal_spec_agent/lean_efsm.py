"""All-rule contracts for the explicit timer-free integer EFSM fragment."""
import hashlib
import json
import re
from pathlib import Path

from protocol_lab.ir import load, model_files
from . import lean_backend as gate

HERE = Path(__file__).resolve().parent
NS = 'FormalSpecAgent.EfsmSubset.'
ST = 'FormalSpecAgent.StateSubset.'
SCOPE = ('All-rule preservation before invariant filtering, pairwise disjointness, '
         'all-state/event coverage and enabling/literal witnesses for the admitted '
         'timer-free integer EFSM fragment. Not C refinement, timers, native overflow, '
         'memory/compiler, reachability or specification interpretation correctness.')


def integer(e, variables, fields, depth=0):
    if depth > 64: raise ValueError('EFSM expression depth exceeded')
    if type(e) is int:
        if not -(2**63) <= e < 2**63: raise ValueError('EFSM literal outside signed64')
        return '(' + ST + 'IntegerExpr.literal ' + gate.number(e) + ')'
    if type(e) is dict and set(e) == {'var'} and e['var'] in variables:
        return '(' + ST + 'IntegerExpr.variable ' + str(variables.index(e['var'])) + ')'
    if type(e) is dict and set(e) == {'event'} and e['event'] in fields:
        return '(' + ST + 'IntegerExpr.field ' + str(fields.index(e['event'])) + ')'
    raise ValueError('Unsupported EFSM integer expression')


def predicate(p, states, variables, fields, depth=0):
    if depth > 64: raise ValueError('EFSM predicate depth exceeded')
    if type(p) is bool: return '(' + NS + 'Predicate.literal ' + str(p).lower() + ')'
    if type(p) is dict and set(p) == {'state'} and p['state'] in states:
        return '(' + NS + 'Predicate.atState ' + str(states.index(p['state'])) + ')'
    if type(p) is not dict or set(p) != {'op', 'args'} or type(p['args']) is not list:
        raise ValueError('Unsupported EFSM predicate')
    op = p['op']; args = p['args']
    if op == 'not' and len(args) == 1:
        return '(' + NS + 'Predicate.negation ' + predicate(args[0], states, variables, fields, depth+1) + ')'
    if len(args) != 2: raise ValueError('EFSM binary predicate arity required')
    if op in ('and', 'or'):
        return '(' + NS + ('Predicate.conjunction ' if op == 'and' else 'Predicate.disjunction ') + ' '.join(predicate(a, states, variables, fields, depth+1) for a in args) + ')'
    if op not in ('eq', 'le', 'ge'): raise ValueError('Unsupported EFSM predicate operator')
    if op == 'ge': args = list(reversed(args))
    return '(' + NS + ('Predicate.equal ' if op == 'eq' else 'Predicate.lessEqual ') + ' '.join(integer(a, variables, fields, depth+1) for a in args) + ')'


def vector(values):
    if type(values) is not list or any(type(n) is not int or not -(2**63) <= n < 2**63 for n in values):
        raise ValueError('Concrete EFSM values must be signed64 integers')
    return '[' + ', '.join(gate.number(n) for n in values) + ']'


def prepare(task_file, workspace, task_sha256, *, draft=False):
    root = Path(workspace).resolve(); task_file = Path(task_file).resolve()
    if not task_file.is_relative_to(root) or gate.sha(task_file) != task_sha256:
        raise ValueError('EFSM task outside workspace or digest mismatch')
    t = json.loads(task_file.read_text())
    keys = {'schema', 'id', 'model', 'model_sha256', 'sources', 'witnesses', 'lean_version', 'foundation_sha256', 'state_semantics_sha256', 'efsm_semantics_sha256', 'adapter_sha256', 'approved_sha256'}
    if set(t) != keys or t['schema'] != 'fsa-lean-efsm-task-v1' or t['lean_version'] != gate.VERSION:
        raise ValueError('Unsupported EFSM task schema/version')
    if type(t['id']) is not str or not re.fullmatch(r'[A-Za-z0-9_-]{1,80}', t['id']): raise ValueError('Invalid EFSM identity')
    for path, pin in [(HERE/'lean/Foundation.lean', t['foundation_sha256']), (HERE/'lean/StateSubset.lean', t['state_semantics_sha256']), (HERE/'lean/EfsmSubset.lean', t['efsm_semantics_sha256']), (Path(__file__).resolve(), t['adapter_sha256'])]:
        if gate.sha(path) != pin: raise ValueError('EFSM semantic/adapter approval epoch changed')
    model_file = gate.inside(root, t['model']); chain = model_files(model_file)
    if any(not p.is_relative_to(root) for p in chain): raise ValueError('EFSM model base escapes workspace')
    if gate.sha(model_file) != t['model_sha256']: raise ValueError('EFSM model digest mismatch')
    paths = [task_file, *chain]; pinned = set()
    if type(t['sources']) is not list or not t['sources']: raise ValueError('Pinned EFSM sources required')
    for row in t['sources']:
        if type(row) is not dict or set(row) != {'path', 'sha256'}: raise ValueError('Bad EFSM source binding')
        p = gate.inside(root, row['path'])
        if gate.sha(p) != row['sha256']: raise ValueError('EFSM source digest mismatch')
        paths.append(p); pinned.add(p)
    if not set(chain[1:]) <= pinned: raise ValueError('Every EFSM base must be pinned')
    m = load(model_file)
    if m['ir_version'] not in ('0.5', '0.6') or m['semantics'] != 'flat-efsm-atomic-ordered-v1' or m['timers'] or m['scope'].get('terminal_states', []):
        raise ValueError('EFSM unit requires atomic-v1 without timers/terminal states')
    variables = list(m['variables']); states = m['states']; events = list(m['events']); messages = list(m['messages']); rules = m['transitions']
    if not 1 <= len(variables) <= 64 or any(v['type'] != 'int' for v in m['variables'].values()): raise ValueError('EFSM unit requires integer variables')
    if not 1 <= len(states) <= 128 or not 1 <= len(rules) <= 512 or not m['invariants']: raise ValueError('EFSM size/invariant profile exceeded')
    for e in m['events'].values():
        if e['origin'] not in ('application', 'network') or len(e['fields']) > 64 or any(k != 'int' for k in e['fields'].values()): raise ValueError('EFSM external integer fields required')
    source = 'import EfsmSubset\n\nnamespace Approved\n\n'
    source += 'def invariants : List ' + NS + 'Predicate :=\n  [' + ', '.join(predicate(inv['assert'], states, variables, []) for inv in m['invariants']) + ']\n\n'
    for i, r in enumerate(rules):
        if r.get('target_cases') or len(r['actions']) > 64: raise ValueError('EFSM target/action profile exceeded')
        fields = list(m['events'][r['event']]['fields']); actions = []
        for a in r['actions']:
            if set(a) == {'set'} and set(a['set']) == {'var', 'value'}:
                x = a['set']; actions.append('(' + ST + 'Action.assign ' + str(variables.index(x['var'])) + ' ' + integer(x['value'], variables, fields) + ')')
            elif set(a) == {'emit'} and set(a['emit']) == {'message', 'fields'}:
                x = a['emit']; schema = m['messages'][x['message']]['fields']
                if len(schema) != 1 or list(schema.values()) != ['int']: raise ValueError('EFSM emits require one integer field')
                actions.append('(' + ST + 'Action.emit ' + str(messages.index(x['message'])) + ' ' + integer(next(iter(x['fields'].values())), variables, fields) + ')')
            else: raise ValueError('Unsupported EFSM action')
        source += 'def rule_' + str(i) + ' : ' + NS + 'Rule :=\n  { source := ' + str(states.index(r['from'])) + ', target := ' + str(states.index(r['to'])) + ', event := ' + str(events.index(r['event'])) + ', guard := ' + predicate(r['guard'], states, variables, fields) + ', actions := [' + ', '.join(actions) + '] }\n\n'
    source += 'def rules : List ' + NS + 'Rule := [' + ', '.join('rule_'+str(i) for i in range(len(rules))) + ']\n\n'
    initial = vector([m['variables'][v]['initial'] for v in variables])
    goals = {'initial_valid': NS + 'invariantsHold invariants ' + str(states.index(m['initial_state'])) + ' ' + initial + ' = true'}
    def context(event):
        fields = list(m['events'][event]['fields'])
        names = ['v'+str(i) for i in range(len(variables))]; fnames = ['f'+str(i) for i in range(len(fields))]
        binders = '∀ ' + ' '.join('('+n+' : Int)' for n in names+fnames) + ', '
        return binders, '['+', '.join(names)+']', '['+', '.join(fnames)+']'
    for i, r in enumerate(rules):
        q, s, env = context(r['event']); rule = 'rule_'+str(i)
        goals['preserve_'+str(i)] = q + NS + 'invariantsHold invariants '+rule+'.source '+s+' = true → '+NS+'guardHolds '+rule+' '+s+' '+env+' = true → '+NS+'invariantsHold invariants '+rule+'.target ('+ST+'work '+rule+'.actions '+s+' '+env+' []).1 = true'
    for i, r in enumerate(rules):
        for j in range(i+1, len(rules)):
            other = rules[j]
            if (r['from'], r['event']) != (other['from'], other['event']): continue
            q, s, env = context(r['event']); a, b = 'rule_'+str(i), 'rule_'+str(j)
            goals['overlap_'+str(i)+'_'+str(j)] = q + NS + 'invariantsHold invariants '+a+'.source '+s+' = true → ¬ ('+NS+'guardHolds '+a+' '+s+' '+env+' = true ∧ '+NS+'guardHolds '+b+' '+s+' '+env+' = true)'
    for state_index, state in enumerate(states):
        for event_index, event in enumerate(events):
            q, s, env = context(event)
            guards = '[' + ', '.join('rule_'+str(i)+'.guard' for i,r in enumerate(rules) if r['from']==state and r['event']==event) + ']'
            goals['cover_'+str(state_index)+'_'+str(event_index)] = q + NS + 'invariantsHold invariants '+str(state_index)+' '+s+' = true → '+NS+'covered '+guards+' '+str(state_index)+' '+s+' '+env+' = true'
    witnesses = t['witnesses']
    if type(witnesses) is not list or len(witnesses) != len(rules): raise ValueError('Exactly one enabling/literal witness per rule required')
    by_rule = {}
    for w in witnesses:
        if type(w) is not dict or set(w) != {'rule', 'values', 'fields', 'after'} or type(w['rule']) is not str or w['rule'] in by_rule: raise ValueError('Duplicate/bad EFSM witness')
        by_rule[w['rule']] = w
    if set(by_rule) != {r['id'] for r in rules}: raise ValueError('EFSM witness/rule coverage differs')
    literal_goals = {}
    for i, r in enumerate(rules):
        w = by_rule[r['id']]; fields = list(m['events'][r['event']]['fields']); after = w['after']
        if type(w['values']) is not dict or set(w['values']) != set(variables) or type(w['fields']) is not dict or set(w['fields']) != set(fields): raise ValueError('EFSM witness variable/field dimensions differ')
        if type(after) is not dict or set(after) != {'state', 'variables', 'emitted'} or after['state'] not in states or type(after['variables']) is not dict or set(after['variables']) != set(variables) or type(after['emitted']) is not list or len(after['emitted']) > 64: raise ValueError('Bad EFSM expected outcome')
        s = vector([w['values'][v] for v in variables]); env = vector([w['fields'][f] for f in fields]); out = vector([after['variables'][v] for v in variables]); emitted = []
        for row in after['emitted']:
            if type(row) is not dict or set(row) != {'message', 'fields'} or row['message'] not in m['messages']: raise ValueError('Bad EFSM expected emission')
            schema = m['messages'][row['message']]['fields']
            if len(schema) != 1 or list(schema.values()) != ['int'] or type(row['fields']) is not dict or set(row['fields']) != set(schema): raise ValueError('Bad EFSM expected message schema')
            value = next(iter(row['fields'].values())); vector([value]); emitted.append('('+str(messages.index(row['message']))+', '+gate.number(value)+')')
        rule = 'rule_'+str(i)
        goals['live_'+str(i)] = NS+'invariantsHold invariants '+rule+'.source '+s+' = true ∧ '+NS+'guardHolds '+rule+' '+s+' '+env+' = true'
        literal_goals['witness_'+str(i)] = NS+'candidate '+rule+' '+s+' '+env+' = ('+str(states.index(after['state']))+', ('+out+', ['+', '.join(emitted)+']))'
    goals.update(literal_goals)
    source += '\n\n'.join('def '+n+' : Prop :=\n  '+s for n,s in goals.items()) + '\n\nend Approved\n'
    if not draft and hashlib.sha256(source.encode()).hexdigest() != t['approved_sha256']: raise ValueError('EFSM statements differ from frozen approval')
    inputs = {'workspace/'+str(p.relative_to(root)):gate.sha(p) for p in paths}
    for p in [Path(__file__).resolve(), HERE/'lean_backend.py', HERE/'lean/Foundation.lean', HERE/'lean/StateSubset.lean', HERE/'lean/EfsmSubset.lean', HERE/'lean/lean-toolchain']:
        inputs['tool/'+str(p.relative_to(HERE))] = gate.sha(p)
    inputs['ir_checker'] = gate.sha(HERE.parent/'protocol_lab/ir.py')
    return source, list(goals), inputs
