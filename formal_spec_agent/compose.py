"""Compose modular IR components into one validated authoritative Protocol IR."""
import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import tempfile

from protocol_lab.ir import validate
from protocol_lab.json_values import same_value
from protocol_lab.model_identity import model_hash

from . import lean_backend as gate

SCHEMA = 'fsa-compose-v1'
RECEIPT_SCHEMA = 'fsa-compose-receipt-v1'
FRAMEWORK_ROOT = Path(__file__).resolve().parents[1]
RECIPE_KEYS = {
    'schema', 'protocol', 'ir_version', 'semantics',
    'initial_state', 'states', 'scope', 'components',
}
OPTIONAL_RECIPE_KEYS = {'description'}
COMPONENT_SECTIONS = (
    'requirements', 'variables', 'events', 'messages', 'timers',
    'transitions', 'invariants', 'states',
)


def _rewrite_expr(expr, var_names, timer_names):
    if type(expr) is not dict:
        return copy.deepcopy(expr)
    if 'var' in expr:
        name = expr['var']
        return {**copy.deepcopy(expr), 'var': var_names.get(name, name)}
    if 'timer_active' in expr:
        name = expr['timer_active']
        return {**copy.deepcopy(expr), 'timer_active': timer_names.get(name, name)}
    if 'op' in expr and 'args' in expr:
        return {
            **copy.deepcopy(expr),
            'args': [_rewrite_expr(a, var_names, timer_names) for a in expr['args']],
        }
    return copy.deepcopy(expr)


def _rewrite_action(action, var_names, timer_names, msg_names):
    if type(action) is not dict or len(action) != 1:
        raise ValueError(f'Invalid component action: {action!r}')
    kind, arg = next(iter(action.items()))
    if kind == 'set':
        target = var_names.get(arg['var'], arg['var'])
        return {'set': {'var': target, 'value': _rewrite_expr(arg['value'], var_names, timer_names)}}
    if kind in ('emit', 'emit_if'):
        msg = msg_names.get(arg['message'], arg['message'])
        out = {
            'message': msg,
            'fields': {k: _rewrite_expr(v, var_names, timer_names) for k, v in arg['fields'].items()},
        }
        if kind == 'emit_if':
            out['when'] = _rewrite_expr(arg['when'], var_names, timer_names)
        return {kind: out}
    if kind in ('arm', 'arm_if'):
        timer = timer_names.get(arg['timer'], arg['timer'])
        out = {'timer': timer, 'delay_ms': _rewrite_expr(arg['delay_ms'], var_names, timer_names)}
        if kind == 'arm_if':
            out['when'] = _rewrite_expr(arg['when'], var_names, timer_names)
        return {kind: out}
    if kind == 'cancel':
        return {'cancel': timer_names.get(arg, arg)}
    if kind == 'cancel_if':
        return {
            'cancel_if': {
                'when': _rewrite_expr(arg['when'], var_names, timer_names),
                'timer': timer_names.get(arg['timer'], arg['timer']),
            }
        }
    raise ValueError(f'Unsupported component action operator: {kind}')


def _rewrite_component(comp, prefix):
    unknown = set(comp) - set(COMPONENT_SECTIONS)
    if unknown:
        raise ValueError(f'Unsupported component sections: {sorted(unknown)}')
    if prefix:
        var_map = {k: f'{prefix}{k}' for k in comp.get('variables', {})}
        event_map = {k: f'{prefix}{k}' for k in comp.get('events', {})}
        msg_map = {k: f'{prefix}{k}' for k in comp.get('messages', {})}
        timer_map = {k: f'{prefix}{k}' for k in comp.get('timers', {})}
        req_map = {k: f'{prefix}{k}' for k in comp.get('requirements', {})}
    else:
        var_map = event_map = msg_map = timer_map = req_map = {}

    out = {
        'states': list(comp.get('states', [])),
        'requirements': {req_map.get(k, k): copy.deepcopy(v) for k, v in comp.get('requirements', {}).items()},
        'variables': {var_map.get(k, k): copy.deepcopy(v) for k, v in comp.get('variables', {}).items()},
        'events': {event_map.get(k, k): copy.deepcopy(v) for k, v in comp.get('events', {}).items()},
        'messages': {msg_map.get(k, k): copy.deepcopy(v) for k, v in comp.get('messages', {}).items()},
        'timers': {},
        'transitions': [],
        'invariants': [],
    }
    for name, timer in comp.get('timers', {}).items():
        if type(timer) is not dict or 'event' not in timer:
            raise ValueError(f'Invalid timer declaration: {name}')
        ev = timer['event']
        out['timers'][timer_map.get(name, name)] = {
            **copy.deepcopy(timer),
            'event': event_map.get(ev, ev),
        }
    for rule in comp.get('transitions', []):
        rewritten = copy.deepcopy(rule)
        if prefix:
            rewritten['id'] = f'{prefix}{rule["id"]}'
        rewritten['event'] = event_map.get(rule['event'], rule['event'])
        rewritten['guard'] = _rewrite_expr(rule['guard'], var_map, timer_map)
        rewritten['actions'] = [_rewrite_action(a, var_map, timer_map, msg_map) for a in rule['actions']]
        rewritten['requirements'] = [req_map.get(r, r) for r in rule['requirements']]
        if 'target_cases' in rule:
            rewritten['target_cases'] = [
                {'when': _rewrite_expr(c['when'], var_map, timer_map), 'to': c['to']}
                for c in rule['target_cases']
            ]
        out['transitions'].append(rewritten)
    for inv in comp.get('invariants', []):
        rewritten = copy.deepcopy(inv)
        if prefix:
            rewritten['id'] = f'{prefix}{inv["id"]}'
        rewritten['assert'] = _rewrite_expr(inv['assert'], var_map, timer_map)
        rewritten['requirements'] = [req_map.get(r, r) for r in inv['requirements']]
        out['invariants'].append(rewritten)
    return out


def _atomic_write_json(path: Path, obj) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = json.dumps(obj, indent=2) + '\n'
    fd, tmp_name = tempfile.mkstemp(dir=path.parent, prefix='.tmp-', suffix='.json')
    try:
        with os.fdopen(fd, 'w', encoding='utf-8') as fh:
            fh.write(payload)
        os.replace(tmp_name, path)
    except Exception:
        if os.path.exists(tmp_name):
            os.unlink(tmp_name)
        raise


def compose(recipe_file, workspace, out_model, receipt_file=None):
    """Merge pinned component IR specs into a validated single Protocol IR."""
    workspace = Path(workspace).resolve()
    recipe_file = Path(recipe_file).resolve()
    out_model = Path(out_model).resolve()
    if not recipe_file.is_relative_to(workspace) or not recipe_file.is_file():
        raise ValueError('Compose recipe must reside inside workspace')
    if out_model.is_relative_to(FRAMEWORK_ROOT) and not out_model.is_relative_to(FRAMEWORK_ROOT / 'examples'):
        raise ValueError('Composed model must not overwrite framework source files')
    if receipt_file is not None:
        receipt_file = Path(receipt_file).resolve()
        if receipt_file.is_relative_to(FRAMEWORK_ROOT) and not receipt_file.is_relative_to(FRAMEWORK_ROOT / 'examples'):
            raise ValueError('Compose receipt must not overwrite framework source files')

    recipe = json.loads(recipe_file.read_text())
    if type(recipe) is not dict or not RECIPE_KEYS <= set(recipe) or set(recipe) - RECIPE_KEYS - OPTIONAL_RECIPE_KEYS:
        raise ValueError('Invalid compose recipe schema keys')
    if recipe['schema'] != SCHEMA:
        raise ValueError('Unsupported compose recipe schema')
    if type(recipe['states']) is not list or not recipe['states']:
        raise ValueError('Compose recipe requires non-empty states list')
    if type(recipe['components']) is not list or not recipe['components']:
        raise ValueError('Compose recipe requires at least one component')

    composed = {
        'ir_version': recipe['ir_version'],
        'semantics': recipe['semantics'],
        'protocol': recipe['protocol'],
        'scope': copy.deepcopy(recipe['scope']),
        'states': list(recipe['states']),
        'initial_state': recipe['initial_state'],
        'requirements': {},
        'variables': {},
        'events': {},
        'messages': {},
        'timers': {},
        'transitions': [],
        'invariants': [],
    }
    state_set = set(composed['states'])
    seen_ids = set()
    seen_rules = set()
    seen_invs = set()
    pinned_components = []

    for entry in recipe['components']:
        if type(entry) is not dict or not {'id', 'path', 'sha256'} <= set(entry) or set(entry) - {'id', 'path', 'sha256', 'prefix'}:
            raise ValueError('Invalid component entry')
        cid = entry['id']
        if type(cid) is not str or not re.fullmatch(r'[A-Za-z0-9_.-]+', cid) or cid in seen_ids:
            raise ValueError(f'Invalid or duplicate component id: {cid!r}')
        seen_ids.add(cid)
        prefix = entry.get('prefix', '')
        if type(prefix) is not str:
            raise ValueError('Component prefix must be a string')
        comp_path = gate.inside(workspace, entry['path'])
        actual_sha = hashlib.sha256(comp_bytes := comp_path.read_bytes()).hexdigest()
        if actual_sha != entry['sha256']:
            raise ValueError(f'Component digest mismatch: {entry["path"]}')
        raw_comp = json.loads(comp_bytes.decode('utf-8'))
        if type(raw_comp) is not dict:
            raise ValueError(f'Component must be a JSON object: {entry["path"]}')
        rewritten = _rewrite_component(raw_comp, prefix)
        extra_states = set(rewritten['states']) - state_set
        if extra_states:
            raise ValueError(f'Component {cid} references states absent from recipe: {sorted(extra_states)}')
        for section in ('requirements', 'variables', 'events', 'messages', 'timers'):
            for name, decl in rewritten[section].items():
                if name in composed[section]:
                    if not same_value(composed[section][name], decl):
                        raise ValueError(f'Conflicting {section} declaration across components: {name}')
                else:
                    composed[section][name] = decl
        for rule in rewritten['transitions']:
            if rule['id'] in seen_rules:
                raise ValueError(f'Duplicate transition id across components: {rule["id"]}')
            seen_rules.add(rule['id'])
            composed['transitions'].append(rule)
        for inv in rewritten['invariants']:
            if inv['id'] in seen_invs:
                raise ValueError(f'Duplicate invariant id across components: {inv["id"]}')
            seen_invs.add(inv['id'])
            composed['invariants'].append(inv)
        pinned_components.append({'id': cid, 'path': entry['path'], 'sha256': actual_sha, 'prefix': prefix})

    validate(composed)
    _atomic_write_json(out_model, composed)
    receipt = {
        'schema': RECEIPT_SCHEMA,
        'protocol': composed['protocol'],
        'recipe_sha256': gate.sha(recipe_file),
        'components': pinned_components,
        'out_model': str(out_model),
        'model_sha256': gate.sha(out_model),
        'model_semantic_sha256': model_hash(composed),
        'counts': {
            'states': len(composed['states']),
            'variables': len(composed['variables']),
            'events': len(composed['events']),
            'messages': len(composed['messages']),
            'timers': len(composed['timers']),
            'transitions': len(composed['transitions']),
            'invariants': len(composed['invariants']),
        },
    }
    if receipt_file is not None:
        _atomic_write_json(receipt_file, receipt)
    return receipt


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('recipe', type=Path)
    p.add_argument('--workspace', type=Path, required=True)
    p.add_argument('--out', type=Path, required=True)
    p.add_argument('--receipt', type=Path)
    a = p.parse_args(argv)
    try:
        r = compose(a.recipe, a.workspace, a.out, a.receipt)
        print(json.dumps(r))
        return 0
    except (ValueError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print(json.dumps({'status': 'rejected', 'error_type': type(error).__name__, 'reason': str(error)}), file=sys.stderr)
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
