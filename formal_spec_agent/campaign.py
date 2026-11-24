"""Agent-agnostic parallel proof/codegen campaign orchestrator backed by Lean 4.35.0."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from contextlib import contextmanager
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import threading
import time
import uuid

from protocol_lab.ir import load, model_files
from protocol_lab.pipeline.runner import run as run_pipeline, verify as verify_pipeline
from protocol_lab.pipeline.task import read as read_json, sha as file_sha

from . import lean_backend as gate
from . import lean_timed_check as timed_check
from . import lean_timed_contracts as timed_contracts
from .providers import DEFAULT_PROVIDER, PROVIDERS, get_provider

SCHEMA = 'fsa-campaign-v1'
BRIEF_SCHEMA = 'fsa-worker-brief-v1'
FRAMEWORK_ROOT = Path(__file__).resolve().parents[1]
CORE_GOALS = (
    'initial_admitted', 'targets_declared', 'arms_declared', 'rule_ids_unique',
    'timer_coverage', 'raw_catalog_exact', 'conflict_catalog_exact',
)
ALLOWED_IMPORTS = {'Approved', *timed_check.MODULES}
ALLOWED_SET_OPTIONS = {'maxRecDepth', 'maxHeartbeats'}
FORBIDDEN_PATTERNS = (
    ('sorry', re.compile(r'\bsorry\b')),
    ('admit', re.compile(r'\badmit\b')),
    ('axiom', re.compile(r'\baxiom\b')),
    ('unsafe', re.compile(r'\bunsafe\b')),
    ('native_decide', re.compile(r'\bnative_decide\b')),
    ('initialize', re.compile(r'\binitialize\b')),
    ('elab', re.compile(r'\belab\b')),
    ('macro', re.compile(r'\bmacro\b')),
    ('syntax', re.compile(r'\bsyntax\b')),
    ('run_tac', re.compile(r'\brun_tac\b')),
    ('run_elab', re.compile(r'\brun_elab\b')),
    ('attribute', re.compile(r'\battribute\b')),
    ('extern_attr', re.compile(r'@\[[^\]]*(?:extern|implemented_by)[^\]]*\]')),
    ('eval_cmd', re.compile(r'#(?:eval|reduce)\b')),
)


def _atomic_write_bytes(path, data):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, tmp_name = tempfile.mkstemp(dir=path.parent, prefix='.tmp-')
    try:
        with os.fdopen(fd, 'wb') as fh:
            fh.write(data)
        os.replace(tmp_name, path)
    except Exception:
        if os.path.exists(tmp_name):
            os.unlink(tmp_name)
        raise


def _atomic_write_json(path, obj):
    _atomic_write_bytes(path, (json.dumps(obj, indent=2) + '\n').encode('utf-8'))


def _assert_outside(target, *forbidden):
    target = Path(target).resolve()
    for root in (FRAMEWORK_ROOT, *(Path(p).resolve() for p in forbidden if p is not None)):
        if target == root or target.is_relative_to(root):
            raise ValueError(f'Path must stay outside {root}: {target}')
    return target


@contextmanager
def _campaign_lock(campaign_dir, name='campaign.lock'):
    lock_path = Path(campaign_dir) / name
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    with lock_path.open('a+', encoding='utf-8') as fh:
        fcntl.flock(fh.fileno(), fcntl.LOCK_EX)
        try:
            yield
        finally:
            fcntl.flock(fh.fileno(), fcntl.LOCK_UN)


def _lean_env(workdir):
    return dict(PATH=os.defpath, LEAN_PATH=str(workdir), LANG='C.UTF-8')


def _check_lean_version(lean):
    tool = shutil.which(str(lean))
    if tool is None:
        raise ValueError(f'Pinned Lean executable unavailable: {lean}')
    tool = str(Path(tool).resolve())
    version = subprocess.check_output([tool, '--version'], text=True, timeout=15).strip()
    if not re.search(r'\bversion ' + re.escape(gate.VERSION) + r'(?:,|\))', version):
        raise ValueError(f'Pinned Lean {gate.VERSION} required, got: {version}')
    return tool, version, gate.sha(tool)


def _core_digests():
    return {m: gate.sha(gate.HERE / 'lean' / f'{m}.lean') for m in timed_check.MODULES}


def _compile_base_cache(campaign_dir, lean):
    tool, version, tool_sha = _check_lean_version(lean)
    campaign_dir = Path(campaign_dir)
    cache = campaign_dir / 'olean_cache'
    core_digests = _core_digests()
    with _campaign_lock(campaign_dir, 'olean_cache.lock'):
        approved_src_path = campaign_dir / 'Approved.lean'
        approved_sha = gate.sha(approved_src_path)
        camp_file = campaign_dir / 'campaign.json'
        if camp_file.is_file():
            pinned_state = read_json(camp_file)
            if pinned_state.get('approved_sha256') != approved_sha:
                raise ValueError('Campaign Approved.lean differs from pinned campaign digest')

        marker = cache / '.ready.json'
        expected_names = (*timed_check.MODULES, 'Approved')
        if marker.is_file():
            info = json.loads(marker.read_text())
            if (
                info.get('approved_sha256') == approved_sha
                and info.get('lean_sha256') == tool_sha
                and info.get('core_lean_sha256') == core_digests
                and all((cache / f'{n}.olean').is_file() for n in expected_names)
            ):
                return tool, version, tool_sha

        cache.mkdir(parents=True, exist_ok=True)
        for existing in cache.glob('*.olean'):
            existing.unlink()
        for mod in timed_check.MODULES:
            dst = cache / f'{mod}.lean'
            if dst.exists():
                dst.chmod(0o644)
            _atomic_write_bytes(dst, (gate.HERE / 'lean' / f'{mod}.lean').read_bytes())
        app_dst = cache / 'Approved.lean'
        if app_dst.exists():
            app_dst.chmod(0o644)
        _atomic_write_bytes(app_dst, approved_src_path.read_bytes())
        env = _lean_env(cache)
        for name in expected_names:
            proc = subprocess.run([tool, '-o', f'{name}.olean', f'{name}.lean'],
                                  cwd=cache, env=env, capture_output=True, text=True, timeout=60)
            if proc.returncode != 0:
                raise ValueError(f'Base Lean module {name} failed: {proc.stderr or proc.stdout}')
        _atomic_write_json(marker, {
            'approved_sha256': approved_sha,
            'lean_sha256': tool_sha,
            'lean_version': version,
            'core_lean_sha256': core_digests,
        })
    return tool, version, tool_sha


def _skeleton(module, goals, kind, metadata):
    lines = ['import Approved']
    if kind == 'core':
        lines.append('import TimedObligations')
    elif kind == 'firing':
        lines.append('import InvariantFootprint')
    lines.extend([
        '',
        f'namespace {module}',
        'open Approved FormalSpecAgent TypedIR TypedMachine TypedFiringContracts TimedObligations',
        '',
    ])
    for goal in goals:
        if kind == 'core' and goal in ('raw_catalog_exact', 'conflict_catalog_exact'):
            lines.append(f'theorem {goal} : Approved.{goal} := by rfl')
        else:
            lines.append(f'theorem {goal} : Approved.{goal} := by')
            lines.append('  sorry -- replace with valid Lean proof')
        lines.append('')
    lines.append(f'end {module}')
    return '\n'.join(lines) + '\n'


def _build_units(model, goals, shard_size, core_digests, approved_sha):
    raw_entries, conflict_groups = timed_contracts.entries(
        type('V', (), {'m': model, 'timers': sorted(model['timers'])})()
    )
    raw_items = []
    for index, timer in raw_entries:
        rule = model['transitions'][index]
        suffix = 'external' if timer is None else f'timer_{timer}'
        goal_name = f'raw_{index}_{suffix}'
        raw_items.append({
            'goal': goal_name,
            'prop': goals[goal_name],
            'rule_index': index,
            'rule_id': rule['id'],
            'from': rule['from'],
            'to': rule['to'],
            'event': rule['event'],
            'timer': timer,
            'term': f'(rule_{index}, {"none" if timer is None else f"(some {timer})"})',
        })

    conflict_items = []
    for index, group in enumerate(conflict_groups):
        goal_name = f'conflict_{index}'
        conflict_items.append({
            'goal': goal_name,
            'prop': goals[goal_name],
            'group_index': index,
            'conflict_def': f'conflictGroup_{index}',
            'rule_ids': [model['transitions'][r]['id'] for r in group],
            'singleton': len(group) == 1,
        })

    def make_unit(unit_id, kind, module, unit_goals, meta):
        key_payload = json.dumps({
            'core': core_digests,
            'approved_sha256': approved_sha,
            'module': module,
            'goals': {g: goals[g] for g in unit_goals},
        }, sort_keys=True).encode()
        return {
            'id': unit_id,
            'kind': kind,
            'module': module,
            'goals': list(unit_goals),
            'metadata': meta,
            'cache_key': hashlib.sha256(key_payload).hexdigest(),
            'status': 'pending',
            'attempts': 0,
            'worker': None,
            'lease_token': None,
            'lease_expires_at': None,
            'last_error': None,
            'verified_sha256': None,
            'axioms': None,
            'from_cache': False,
        }

    units = [
        make_unit('core_contracts', 'core', 'CoreContracts', CORE_GOALS, {}),
    ]
    for offset in range(0, len(conflict_items), shard_size):
        chunk = conflict_items[offset:offset + shard_size]
        idx = offset // shard_size
        units.append(make_unit(
            f'conflict_shard_{idx:03d}',
            'conflict',
            f'ConflictShard{idx:03d}',
            [item['goal'] for item in chunk],
            {'items': chunk},
        ))

    # Keep raw_items in exact Approved.rawCatalog transition order across all firing shards.
    for offset in range(0, len(raw_items), shard_size):
        chunk = raw_items[offset:offset + shard_size]
        idx = offset // shard_size
        units.append(make_unit(
            f'firing_shard_{idx:03d}',
            'firing',
            f'FiringShard{idx:03d}',
            [item['goal'] for item in chunk],
            {'items': chunk},
        ))
    return units, raw_items, conflict_items


def init_campaign(workspace, model_path, campaign_dir, *, lean='lean', skip_precompile=False,
                  shard_size=8, max_attempts=5, cache_dir=None):
    """Initialize a shard workgraph and immutable Approved.lean view from a Protocol IR."""
    workspace = Path(workspace).resolve()
    model_path = Path(model_path).resolve()
    if not model_path.is_relative_to(workspace) or not model_path.is_file():
        raise ValueError('Model must reside inside workspace')
    if shard_size < 1 or max_attempts < 1:
        raise ValueError('shard_size and max_attempts must be >= 1')
    campaign_dir = _assert_outside(campaign_dir, workspace)
    if campaign_dir.exists():
        raise FileExistsError(f'Campaign directory already exists: {campaign_dir}')
    cache_root = _assert_outside(cache_dir, workspace) if cache_dir else (campaign_dir / 'cache')

    model = load(model_path)
    source_model_files = {p.relative_to(model_path.parent).as_posix(): gate.sha(p) for p in model_files(model_path)}
    approved_src, goals = timed_contracts.render(model)
    core_digests = _core_digests()

    campaign_dir.mkdir(parents=True)
    for sub in ('briefs', 'verified', 'attempts', 'staging', 'olean_cache'):
        (campaign_dir / sub).mkdir()
    cache_root.mkdir(parents=True, exist_ok=True)

    pinned_model = campaign_dir / 'model.json'
    _atomic_write_bytes(pinned_model, (json.dumps(model, indent=2) + '\n').encode('utf-8'))
    model_sha = gate.sha(model_path)
    pinned_model.chmod(0o444)

    approved_path = campaign_dir / 'Approved.lean'
    _atomic_write_bytes(approved_path, approved_src.encode('utf-8'))
    approved_sha = gate.sha(approved_path)
    approved_path.chmod(0o444)

    units, raw_items, conflict_items = _build_units(model, goals, shard_size, core_digests, approved_sha)
    precompiled = False
    lean_info = None
    if not skip_precompile:
        _, version, tool_sha = _compile_base_cache(campaign_dir, lean)
        precompiled = True
        lean_info = {'version': version, 'sha256': tool_sha}

    state = {
        'schema': SCHEMA,
        'created_at': time.time(),
        'workspace': str(workspace),
        'source_model': model_path.relative_to(workspace).as_posix(),
        'source_model_sha256': model_sha,
        'source_model_files': source_model_files,
        'approved_sha256': approved_sha,
        'core_lean_sha256': core_digests,
        'cache_dir': str(cache_root),
        'shard_size': shard_size,
        'max_attempts': max_attempts,
        'precompiled': precompiled,
        'lean': lean_info,
        'raw_order': [{'goal': r['goal'], 'term': r['term'], 'module': u['module']}
                      for u in units if u['kind'] == 'firing' for r in u['metadata']['items']],
        'conflict_order': [{'goal': c['goal'], 'conflict_def': c['conflict_def'], 'module': u['module']}
                           for u in units if u['kind'] == 'conflict' for c in u['metadata']['items']],
        'units': units,
    }
    with _campaign_lock(campaign_dir):
        _atomic_write_json(campaign_dir / 'campaign.json', state)
    return status_campaign(campaign_dir)


def _reclaim_expired(state, now=None):
    now = time.time() if now is None else now
    changed = False
    for unit in state['units']:
        if unit['status'] == 'claimed' and unit['lease_expires_at'] is not None and unit['lease_expires_at'] <= now:
            unit['status'] = 'failed' if unit['attempts'] > 0 else 'pending'
            unit['worker'] = None
            unit['lease_token'] = None
            unit['lease_expires_at'] = None
            unit['last_error'] = unit['last_error'] or 'Worker lease expired'
            changed = True
    return changed


def _is_ready(unit, max_attempts):
    if unit['status'] == 'pending':
        return True
    return unit['status'] == 'failed' and unit['attempts'] < max_attempts


def status_campaign(campaign_dir):
    """Return current counts, active leases, and ready units."""
    campaign_dir = Path(campaign_dir).resolve()
    with _campaign_lock(campaign_dir):
        state = read_json(campaign_dir / 'campaign.json')
        if _reclaim_expired(state):
            _atomic_write_json(campaign_dir / 'campaign.json', state)
    counts = {k: 0 for k in ('pending', 'claimed', 'verified', 'failed', 'exhausted')}
    for u in state['units']:
        counts[u['status']] = counts.get(u['status'], 0) + 1
    ready = [u['id'] for u in state['units'] if _is_ready(u, state['max_attempts'])]
    return {
        'schema': SCHEMA,
        'campaign': str(campaign_dir),
        'source_model': state['source_model'],
        'source_model_sha256': state['source_model_sha256'],
        'total_units': len(state['units']),
        'counts': counts,
        'ready_units': ready,
        'ready_to_assemble': counts['verified'] == len(state['units']),
        'units': [
            {
                'id': u['id'],
                'module': u['module'],
                'kind': u['kind'],
                'status': u['status'],
                'goals': len(u['goals']),
                'attempts': u['attempts'],
                'worker': u['worker'],
                'from_cache': u['from_cache'],
            }
            for u in state['units']
        ],
    }


def _find_unit(state, unit_id):
    for unit in state['units']:
        if unit['id'] == unit_id:
            return unit
    raise ValueError(f'Unknown campaign unit: {unit_id}')


def claim_unit(campaign_dir, worker_id, *, unit_id=None, lease_seconds=600):
    """Atomically lease one ready proof unit and emit its worker brief."""
    campaign_dir = Path(campaign_dir).resolve()
    if not re.fullmatch(r'[A-Za-z0-9_.-]{1,64}', worker_id):
        raise ValueError(f'Invalid worker ID: {worker_id}')
    if lease_seconds <= 0:
        raise ValueError('lease_seconds must be positive')

    with _campaign_lock(campaign_dir):
        state = read_json(campaign_dir / 'campaign.json')
        _reclaim_expired(state)
        max_attempts = state['max_attempts']
        target = None
        if unit_id is not None:
            candidate = _find_unit(state, unit_id)
            if _is_ready(candidate, max_attempts):
                target = candidate
        else:
            for candidate in state['units']:
                if _is_ready(candidate, max_attempts):
                    target = candidate
                    break
        if target is None:
            return None
        now = time.time()
        token = str(uuid.uuid4())
        target['status'] = 'claimed'
        target['worker'] = worker_id
        target['lease_token'] = token
        target['lease_expires_at'] = now + lease_seconds
        target['attempts'] += 1
        _atomic_write_json(campaign_dir / 'campaign.json', state)

        brief = {
            'schema': BRIEF_SCHEMA,
            'campaign': str(campaign_dir),
            'unit_id': target['id'],
            'kind': target['kind'],
            'module': target['module'],
            'attempt': target['attempts'],
            'max_attempts': state['max_attempts'],
            'worker': worker_id,
            'lease_token': token,
            'cache_key': target['cache_key'],
            'goals': target['goals'],
            'metadata': target['metadata'],
            'allowed_imports': sorted(ALLOWED_IMPORTS),
            'forbidden_patterns': [name for name, _ in FORBIDDEN_PATTERNS],
            'allowed_axioms': sorted(gate.AXIOMS),
            'approved_lean_path': str(campaign_dir / 'Approved.lean'),
            'model_path': str(campaign_dir / 'model.json'),
            'olean_dir': str(campaign_dir / 'olean_cache'),
            'staging_path': str(campaign_dir / 'staging' / f'{target["id"]}-{worker_id}.lean'),
            'last_error': target['last_error'],
            'skeleton_lean': _skeleton(target['module'], target['goals'], target['kind'], target['metadata']),
        }
        brief_path = campaign_dir / 'briefs' / f'{target["id"]}.json'
        _atomic_write_json(brief_path, brief)
        brief['brief_path'] = str(brief_path)
    return brief


def release_unit(campaign_dir, unit_id, *, worker_id=None, error_note=None):
    """Release an active worker lease without burning retry state inconsistently."""
    campaign_dir = Path(campaign_dir).resolve()
    with _campaign_lock(campaign_dir):
        state = read_json(campaign_dir / 'campaign.json')
        unit = _find_unit(state, unit_id)
        if unit['status'] != 'claimed':
            raise ValueError(f'Unit is not claimed: {unit_id}')
        if worker_id is not None and unit['worker'] != worker_id:
            raise ValueError(f'Unit {unit_id} is claimed by {unit["worker"]}, not {worker_id}')
        unit['status'] = 'failed' if unit['attempts'] > 0 else 'pending'
        if unit['attempts'] >= state['max_attempts']:
            unit['status'] = 'exhausted'
        unit['worker'] = None
        unit['lease_token'] = None
        unit['lease_expires_at'] = None
        if error_note:
            unit['last_error'] = error_note[:4000]
        _atomic_write_json(campaign_dir / 'campaign.json', state)
        return {'status': unit['status'], 'unit_id': unit_id, 'attempts': unit['attempts']}


def _strip_lean_comments(source_text):
    """Strip Lean line (`--`) and nested block (`/- ... -/`) comments, preserving strings."""
    out = []
    i = 0
    n = len(source_text)
    block_depth = 0
    in_string = False
    while i < n:
        ch = source_text[i]
        nxt = source_text[i + 1] if i + 1 < n else ''
        if block_depth > 0:
            if ch == '/' and nxt == '-':
                block_depth += 1
                i += 2
            elif ch == '-' and nxt == '/':
                block_depth -= 1
                i += 2
            else:
                if ch == '\n':
                    out.append('\n')
                i += 1
            continue
        if in_string:
            out.append(ch)
            if ch == '\\' and i + 1 < n:
                out.append(nxt)
                i += 2
                continue
            if ch == '"':
                in_string = False
            i += 1
            continue
        if ch == '-' and nxt == '-':
            while i < n and source_text[i] != '\n':
                i += 1
            continue
        if ch == '/' and nxt == '-':
            block_depth = 1
            i += 2
            continue
        if ch == '"':
            in_string = True
        out.append(ch)
        i += 1
    if block_depth != 0:
        raise ValueError('Unterminated block comment in candidate Lean file')
    return ''.join(out)


def _validate_candidate_source(source_text):
    cleaned = _strip_lean_comments(source_text)
    for label, pattern in FORBIDDEN_PATTERNS:
        if pattern.search(cleaned):
            raise ValueError(f'Candidate Lean proof contains forbidden construct: {label}')

    if re.search(r'\bnamespace\s+(?:Approved|Audit_)', cleaned):
        raise ValueError('Candidate Lean proof must not declare reserved namespace')

    for match in re.finditer(r'\bset_option\s+([^\s]+)\s+([^\s]+)', cleaned):
        opt, val = match.group(1), match.group(2)
        if opt not in ALLOWED_SET_OPTIONS or not re.fullmatch(r'[1-9][0-9]*', val):
            raise ValueError(f'Disallowed set_option in worker module: set_option {opt} {val}')

    for raw_stmt in re.split(r'[;\n]', cleaned):
        stmt = raw_stmt.strip()
        if not stmt:
            continue
        if re.search(r'(?:^|\s)(?:public\s+|scoped\s+)?import\b', stmt):
            m = re.fullmatch(r'import\s+([A-Za-z][A-Za-z0-9_.]*(?:\s+[A-Za-z][A-Za-z0-9_.]*)*)', stmt)
            if not m:
                raise ValueError(f'Malformed import statement: {stmt}')
            bad = [dep for dep in m.group(1).split() if dep not in ALLOWED_IMPORTS]
            if bad:
                raise ValueError(f'Disallowed imports in worker module: {bad}')


def _run_lean_verification(campaign_dir, unit, source_bytes, tool):
    module = unit['module']
    goals = unit['goals']
    audit_lines = [
        'import Approved',
        f'import {module}',
        f'namespace Audit_{module}',
    ]
    for g in goals:
        audit_lines.append(f'theorem check_{g} : Approved.{g} := {module}.{g}')
    for g in goals:
        audit_lines.append(f'#print axioms Audit_{module}.check_{g}')
    audit_lines.append(f'end Audit_{module}')
    audit_src = '\n'.join(audit_lines) + '\n'

    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp)
        cache = Path(campaign_dir) / 'olean_cache'
        for name in (*timed_check.MODULES, 'Approved'):
            (work / f'{name}.lean').symlink_to(cache / f'{name}.lean')
            (work / f'{name}.olean').symlink_to(cache / f'{name}.olean')
        mod_file = work / f'{module}.lean'
        mod_file.write_bytes(source_bytes)
        mod_file.chmod(0o444)
        audit_file = work / f'Audit_{module}.lean'
        audit_file.write_text(audit_src, encoding='utf-8')
        audit_file.chmod(0o444)

        env = _lean_env(work)
        try:
            mod_proc = subprocess.run([tool, '-o', f'{module}.olean', f'{module}.lean'],
                                      cwd=work, env=env, capture_output=True, text=True, timeout=60)
        except subprocess.TimeoutExpired:
            return False, 'Lean wall-clock timeout compiling module', None
        if mod_proc.returncode != 0:
            diag = (mod_proc.stderr or mod_proc.stdout or 'Lean module compilation failed').strip()
            return False, diag, None

        try:
            aud_proc = subprocess.run([tool, '-o', f'Audit_{module}.olean', f'Audit_{module}.lean'],
                                      cwd=work, env=env, capture_output=True, text=True, timeout=30)
        except subprocess.TimeoutExpired:
            return False, 'Lean wall-clock timeout in axiom audit', None
        if aud_proc.returncode != 0:
            diag = (aud_proc.stderr or aud_proc.stdout or 'Lean audit failed').strip()
            return False, diag, None

        axioms = {}
        try:
            for g in goals:
                axioms[g] = gate.read_axioms(aud_proc.stdout, f'Audit_{module}.check_{g}')
        except ValueError as err:
            return False, str(err), None
        return True, '', axioms


def submit_unit(campaign_dir, unit_id, source_path, *, lean='lean', worker_id=None, lease_token=None):
    """Independently verify candidate Lean module under Lean 4.35.0 and axiom audit."""
    campaign_dir = Path(campaign_dir).resolve()
    source_path = Path(source_path).resolve()
    if not source_path.is_file():
        raise FileNotFoundError(f'Candidate Lean file missing: {source_path}')
    source_bytes = source_path.read_bytes()
    if len(source_bytes) > 512_000:
        raise ValueError('Candidate Lean file exceeds 512 KiB size cap')
    source_text = source_bytes.decode('utf-8')

    with _campaign_lock(campaign_dir):
        state = read_json(campaign_dir / 'campaign.json')
        unit = _find_unit(state, unit_id)
        if unit['status'] == 'exhausted':
            raise ValueError(f'Unit exhausted max attempts: {unit_id}')
        if unit['status'] == 'verified':
            raise ValueError(f'Unit already verified: {unit_id}')
        if unit['status'] == 'claimed':
            if not worker_id or not lease_token:
                raise ValueError(f'Unit {unit_id} is actively claimed by {unit["worker"]}; matching worker and lease_token required')
            if unit['worker'] != worker_id or unit['lease_token'] != lease_token:
                raise ValueError(f'Lease token or worker mismatch for {unit_id}')
        elif lease_token is not None or worker_id is not None:
            raise ValueError(f'Lease is no longer active for {unit_id} (status={unit["status"]})')
        unit_snapshot = json.loads(json.dumps(unit))

    _validate_candidate_source(source_text)
    tool, _, _ = _compile_base_cache(campaign_dir, lean)
    ok, diag, axioms = _run_lean_verification(campaign_dir, unit_snapshot, source_bytes, tool)

    verified_sha = hashlib.sha256(source_bytes).hexdigest()
    cache_root = Path(state['cache_dir'])
    cache_entry_dir = cache_root / unit_snapshot['cache_key']

    with _campaign_lock(campaign_dir):
        state = read_json(campaign_dir / 'campaign.json')
        unit = _find_unit(state, unit_id)
        if lease_token is not None:
            if unit['status'] != 'claimed' or unit['lease_token'] != lease_token or unit['worker'] != worker_id:
                raise ValueError(f'Stale submission for {unit_id}: lease expired or reclaimed')
        else:
            if unit['status'] in ('claimed', 'verified', 'exhausted'):
                raise ValueError(f'Cannot overwrite {unit["status"]} unit {unit_id} without matching lease')
            unit['attempts'] += 1

        unit['worker'] = None
        unit['lease_token'] = None
        unit['lease_expires_at'] = None
        if ok:
            dest = campaign_dir / 'verified' / f'{unit["module"]}.lean'
            if dest.exists():
                dest.chmod(0o644)
            _atomic_write_bytes(dest, source_bytes)
            dest.chmod(0o444)
            with _campaign_lock(cache_root, 'cache.lock'):
                cache_entry_dir.mkdir(parents=True, exist_ok=True)
                cache_mod = cache_entry_dir / f'{unit["module"]}.lean'
                _atomic_write_bytes(cache_mod, source_bytes)
                _atomic_write_json(cache_entry_dir / 'receipt.json', {
                    'cache_key': unit['cache_key'],
                    'module': unit['module'],
                    'sha256': verified_sha,
                    'axioms': axioms,
                })
            unit['status'] = 'verified'
            unit['last_error'] = None
            unit['verified_sha256'] = verified_sha
            unit['axioms'] = axioms
        else:
            attempt_log = campaign_dir / 'attempts' / f'{unit_id}-{unit["attempts"]:02d}.stderr'
            _atomic_write_bytes(attempt_log, (diag + '\n').encode('utf-8'))
            unit['status'] = 'exhausted' if unit['attempts'] >= state['max_attempts'] else 'failed'
            unit['last_error'] = diag[:4000]
        _atomic_write_json(campaign_dir / 'campaign.json', state)

    return {
        'status': 'verified' if ok else unit['status'],
        'unit_id': unit_id,
        'module': unit_snapshot['module'],
        'sha256': verified_sha if ok else None,
        'axioms': axioms,
        'error': None if ok else diag[:4000],
    }


def _try_cache_hits(campaign_dir, tool):
    with _campaign_lock(campaign_dir):
        state = read_json(campaign_dir / 'campaign.json')
        cache_root = Path(state['cache_dir'])
        candidates = [
            json.loads(json.dumps(u))
            for u in state['units']
            if _is_ready(u, state['max_attempts']) and (cache_root / u['cache_key'] / f'{u["module"]}.lean').is_file()
        ]

    reused = []
    for unit_snap in candidates:
        uid = unit_snap['id']
        mod = unit_snap['module']
        entry_dir = cache_root / unit_snap['cache_key']
        cache_mod = entry_dir / f'{mod}.lean'
        receipt_file = entry_dir / 'receipt.json'
        with _campaign_lock(cache_root, 'cache.lock'):
            if not cache_mod.is_file() or not receipt_file.is_file():
                continue
            try:
                source_bytes = cache_mod.read_bytes()
                receipt = json.loads(receipt_file.read_text(encoding='utf-8'))
            except (OSError, json.JSONDecodeError):
                continue
            verified_sha = hashlib.sha256(source_bytes).hexdigest()
            if verified_sha != receipt.get('sha256'):
                continue

        try:
            source_text = source_bytes.decode('utf-8')
            _validate_candidate_source(source_text)
        except (UnicodeDecodeError, ValueError):
            continue

        ok, _, axioms = _run_lean_verification(campaign_dir, unit_snap, source_bytes, tool)
        if not ok:
            continue

        with _campaign_lock(campaign_dir):
            state = read_json(campaign_dir / 'campaign.json')
            unit = _find_unit(state, uid)
            if not _is_ready(unit, state['max_attempts']):
                continue
            dest = campaign_dir / 'verified' / f'{mod}.lean'
            if dest.exists():
                dest.chmod(0o644)
            _atomic_write_bytes(dest, source_bytes)
            dest.chmod(0o444)
            unit['status'] = 'verified'
            unit['last_error'] = None
            unit['verified_sha256'] = verified_sha
            unit['axioms'] = axioms
            unit['from_cache'] = True
            _atomic_write_json(campaign_dir / 'campaign.json', state)
            reused.append(uid)
    return reused


def run_workers(campaign_dir, *, lean='lean', concurrency=4, backend='command', cmd_template=None,
                provider_name=DEFAULT_PROVIDER, provider_model=None, ledger=None, credential_file=None,
                max_calls=24, max_tokens=8192, provider=None):
    """Drive parallel claim -> worker -> submit loops until verified or exhausted."""
    campaign_dir = Path(campaign_dir).resolve()
    if concurrency < 1:
        raise ValueError('concurrency must be >= 1')

    with _campaign_lock(campaign_dir):
        state = read_json(campaign_dir / 'campaign.json')

    if backend == 'command':
        if not cmd_template:
            raise ValueError('--cmd template required for --backend command')
        raw_tokens = shlex.split(cmd_template)
        if not raw_tokens:
            raise ValueError('--cmd template must not be empty')
        approved_src = ''
    elif backend == 'provider':
        if provider is None:
            provider = get_provider(provider_name)
        if not provider_model or not ledger or not credential_file:
            raise ValueError('--model, --ledger, and --credential-file required for --backend provider')
        _assert_outside(ledger, state['workspace'], campaign_dir)
        _assert_outside(credential_file, state['workspace'], campaign_dir)
        approved_src = (campaign_dir / 'Approved.lean').read_text(encoding='utf-8')
    else:
        raise ValueError(f'Unsupported worker backend: {backend}')

    tool, _, _ = _compile_base_cache(campaign_dir, lean)
    cache_reused = _try_cache_hits(campaign_dir, tool)
    abort_provider = threading.Event()

    def worker_loop(worker_idx):
        worker_id = f'worker-{worker_idx}'
        while True:
            if abort_provider.is_set():
                return
            brief = claim_unit(campaign_dir, worker_id)
            if brief is None:
                return
            if abort_provider.is_set():
                try:
                    release_unit(campaign_dir, brief['unit_id'], worker_id=worker_id, error_note='Aborted on sibling provider failure')
                except ValueError:
                    pass
                return
            uid = brief['unit_id']
            mod = brief['module']
            stage_out = Path(brief['staging_path'])
            if backend == 'command':
                try:
                    argv = [
                        tok.replace('{brief}', brief['brief_path'])
                           .replace('{out}', str(stage_out))
                           .replace('{unit}', uid)
                           .replace('{module}', mod)
                           .replace('{worker}', worker_id)
                        for tok in raw_tokens
                    ]
                    proc = subprocess.run(argv, capture_output=True, text=True, timeout=300)
                    if proc.returncode != 0 or not stage_out.is_file():
                        release_unit(campaign_dir, uid, worker_id=worker_id,
                                     error_note=f'Worker command exited {proc.returncode}: {(proc.stderr or proc.stdout)[:1000]}')
                        continue
                    submit_unit(campaign_dir, uid, stage_out, lean=lean,
                                worker_id=worker_id, lease_token=brief['lease_token'])
                except Exception as exc:
                    try:
                        release_unit(campaign_dir, uid, worker_id=worker_id, error_note=f'{type(exc).__name__}: {exc}')
                    except ValueError:
                        pass
            else:
                try:
                    user_payload = {
                        'brief': {k: brief[k] for k in ('unit_id', 'kind', 'module', 'goals', 'metadata', 'allowed_imports', 'forbidden_patterns', 'skeleton_lean', 'last_error')},
                        'approved_lean_excerpt': approved_src[:48000],
                    }
                    messages = [
                        {
                            'role': 'system',
                            'content': (
                                'Generate a complete Lean 4.35.0 module file implementing ONLY the requested theorems. '
                                'Return JSON object {"lean_source": "<source>"}. Never use sorry, admit, axiom, unsafe, or disallowed imports.'
                            ),
                        },
                        {'role': 'user', 'content': json.dumps(user_payload)},
                    ]
                    receipt = provider(messages, Path(ledger), Path(credential_file), model=provider_model,
                                       max_tokens=max_tokens, max_calls=max_calls,
                                       thinking='disabled', reasoning_effort=None, timeout=300)
                    resp_file = (Path(ledger) / receipt['response_file']).resolve()
                    if not resp_file.is_relative_to(Path(ledger).resolve()):
                        raise ValueError('Provider response escapes ledger')
                    resp = json.loads(resp_file.read_text())['response']
                    if type(resp) is not dict or type(resp.get('lean_source')) is not str:
                        raise ValueError('Provider response missing lean_source string')
                    stage_out.write_text(resp['lean_source'], encoding='utf-8')
                except Exception as exc:
                    # Uncertain provider/transport failures halt all threads immediately so no silent paid retries occur.
                    abort_provider.set()
                    try:
                        release_unit(campaign_dir, uid, worker_id=worker_id,
                                     error_note=f'Provider uncertainty: {type(exc).__name__}: {exc}')
                    except ValueError:
                        pass
                    return
                try:
                    submit_unit(campaign_dir, uid, stage_out, lean=lean,
                                worker_id=worker_id, lease_token=brief['lease_token'])
                except ValueError as exc:
                    # Static screening rejections (e.g., sorry / bad import from LLM) are repairable attempts.
                    try:
                        release_unit(campaign_dir, uid, worker_id=worker_id, error_note=str(exc))
                    except ValueError:
                        pass

    with ThreadPoolExecutor(max_workers=concurrency) as pool:
        list(pool.map(worker_loop, range(concurrency)))

    summary = status_campaign(campaign_dir)
    summary['cache_reused'] = cache_reused
    return summary


def _render_timed_proof(state):
    core_mod = 'CoreContracts'
    conflict_mods = [u['module'] for u in state['units'] if u['kind'] == 'conflict']
    firing_mods = [u['module'] for u in state['units'] if u['kind'] == 'firing']
    lines = ['import Approved', f'import {core_mod}']
    lines.extend(f'import {m}' for m in conflict_mods)
    lines.extend(f'import {m}' for m in firing_mods)
    lines.extend([
        '',
        'namespace TimedProof',
        'open Approved FormalSpecAgent BatchTotality TimedObligations TypedFiringContracts',
        '',
        f'theorem initial : Approved.initial_admitted := {core_mod}.initial_admitted',
        '',
        'private theorem each_append {α : Type} {items rest : List α} {p : α → Prop}',
        '    (left : Each p items) (right : Each p rest) : Each p (items ++ rest) := by',
        '  induction items with',
        '  | nil => exact right',
        '  | cons _ _ ih => exact ⟨left.1, ih left.2⟩',
        '',
    ])

    conflict_units = [u for u in state['units'] if u['kind'] == 'conflict']
    c_shard_names = []
    for u in conflict_units:
        sname = f'_cshard_{u["module"]}'
        c_shard_names.append(sname)
        defs = ', '.join(item['conflict_def'] for item in u['metadata']['items'])
        proofs = ', '.join(f'{u["module"]}.{item["goal"]}' for item in u['metadata']['items'])
        lines.append(f'private theorem {sname} : Each (ConflictFree model) [{defs}] :=')
        lines.append(f'  ⟨{proofs}, trivial⟩' if proofs else '  trivial')
        lines.append('')

    def fold_append(names):
        if len(names) == 1:
            return names[0]
        mid = len(names) // 2
        return f'(each_append {fold_append(names[:mid])} {fold_append(names[mid:])})'

    lines.append('private theorem conflicts_checked : Each (ConflictFree model) (conflictChecks model) := by')
    lines.append(f'  rw [{core_mod}.conflict_catalog_exact]')
    lines.append('  unfold Approved.conflictCatalog')
    lines.append(f'  exact {fold_append(c_shard_names)}' if c_shard_names else '  trivial')
    lines.append('')

    firing_units = [u for u in state['units'] if u['kind'] == 'firing']
    f_shard_names = []
    for u in firing_units:
        sname = f'_fshard_{u["module"]}'
        f_shard_names.append(sname)
        terms = ', '.join(item['term'] for item in u['metadata']['items'])
        proofs = ', '.join(f'{u["module"]}.{item["goal"]}' for item in u['metadata']['items'])
        lines.append(f'private theorem {sname} : Each (fun p => FiringPreserves model p.1 p.2) [{terms}] :=')
        lines.append(f'  ⟨{proofs}, trivial⟩' if proofs else '  trivial')
        lines.append('')

    lines.append('theorem preservation :')
    lines.append('    Each (fun p => FiringPreserves model p.1 p.2) (rawChecks model declaredTimers) := by')
    lines.append(f'  rw [{core_mod}.raw_catalog_exact]')
    lines.append('  unfold Approved.rawCatalog')
    lines.append(f'  exact {fold_append(f_shard_names)}' if f_shard_names else '  trivial')
    lines.extend([
        '',
        'theorem timers : TimerContracts model declaredStates declaredTimers :=',
        '  timer_contracts_from_checks model declaredStates declaredTimers',
        f'    {core_mod}.targets_declared {core_mod}.arms_declared',
        f'    {core_mod}.rule_ids_unique {core_mod}.timer_coverage',
        '    preservation conflicts_checked',
        '',
        'end TimedProof',
    ])
    return '\n'.join(lines) + '\n'


def _update_flow_manifest(workspace, flow_path, model_rel, manifest_path, module_names):
    flow_path = Path(flow_path).resolve()
    if not flow_path.is_relative_to(workspace):
        raise ValueError('Flow file must reside inside workspace')
    flow = json.loads(flow_path.read_text())
    sources = list(flow.get('sources', []))
    by_path = {s['path']: s for s in sources}
    by_id = {s['id']: s for s in sources}

    def upsert(sid, rel_path):
        digest = gate.sha(workspace / rel_path)
        entry = by_path.get(rel_path) or by_id.get(sid)
        if entry is not None:
            entry['path'] = rel_path
            entry['sha256'] = digest
            entry['uri_aliases'] = [rel_path]
            by_path[rel_path] = entry
        else:
            entry = {'id': sid, 'path': rel_path, 'sha256': digest, 'version': '1', 'uri_aliases': [rel_path]}
            sources.append(entry)
            by_path[rel_path] = entry
            by_id[sid] = entry
        return digest

    lean_rel = manifest_path.parent.relative_to(workspace).as_posix()
    if model_rel in by_path:
        upsert(by_path[model_rel]['id'], model_rel)
    manifest_rel = f'{lean_rel}/manifest.json'
    manifest_sha = upsert('lean_manifest', manifest_rel)
    for mod in module_names:
        upsert(mod, f'{lean_rel}/{mod}.lean')

    flow['sources'] = sources
    flow['formal'] = {
        'strategy': 'lean-timed',
        'manifest': manifest_rel,
        'manifest_sha256': manifest_sha,
    }
    _atomic_write_json(flow_path, flow)


def assemble_campaign(campaign_dir, out_workspace, *, lean_dir_rel='lean', update_flow=None,
                      run_flow=False, flow_out=None, lean='lean'):
    """Assemble all verified shard proofs into TimedProof.lean + v2 manifest (and optionally run 10-stage flow)."""
    campaign_dir = Path(campaign_dir).resolve()
    out_workspace = Path(out_workspace).resolve()
    if out_workspace.is_relative_to(FRAMEWORK_ROOT) and not out_workspace.is_relative_to(FRAMEWORK_ROOT / 'examples'):
        raise ValueError('Workspace cannot modify framework core packages')

    with _campaign_lock(campaign_dir):
        state = read_json(campaign_dir / 'campaign.json')
    not_done = [u['id'] for u in state['units'] if u['status'] != 'verified']
    if not_done:
        raise ValueError(f'Campaign incomplete; unverified units remain: {not_done}')

    model_rel = state['source_model']
    model_file = out_workspace / model_rel
    if not model_file.is_file() or gate.sha(model_file) != state['source_model_sha256']:
        raise ValueError('Target workspace model differs from pinned campaign model')

    pinned_files = state.get('source_model_files') or {model_file.name: state['source_model_sha256']}
    actual_chain = {p.relative_to(model_file.parent).as_posix(): gate.sha(p) for p in model_files(model_file)}
    if actual_chain != pinned_files:
        raise ValueError('Target workspace model inheritance chain differs from pinned campaign')

    lean_dir = (out_workspace / lean_dir_rel).resolve()
    if not lean_dir.is_relative_to(out_workspace):
        raise ValueError('lean directory escapes workspace')
    lean_dir.mkdir(parents=True, exist_ok=True)

    ordered_shards = [u['module'] for u in state['units']]
    for u in state['units']:
        src = campaign_dir / 'verified' / f'{u["module"]}.lean'
        if not src.is_file() or gate.sha(src) != u['verified_sha256']:
            raise ValueError(f'Verified shard tampered or missing: {u["module"]}')
        _atomic_write_bytes(lean_dir / f'{u["module"]}.lean', src.read_bytes())

    timed_proof_path = lean_dir / 'TimedProof.lean'
    _atomic_write_bytes(timed_proof_path, _render_timed_proof(state).encode('utf-8'))
    all_modules = [*ordered_shards, 'TimedProof']

    compile_groups = [ordered_shards[i:i + 2] for i in range(0, len(ordered_shards), 2)]
    compile_groups.append(['TimedProof'])
    manifest_obj = {
        'schema': timed_check.V2_SCHEMA,
        'model': pinned_files,
        'modules': [{'module': m, 'sha256': gate.sha(lean_dir / f'{m}.lean')} for m in all_modules],
        'compile_groups': compile_groups,
    }
    manifest_path = lean_dir / 'manifest.json'
    _atomic_write_json(manifest_path, manifest_obj)
    manifest_sha = gate.sha(manifest_path)

    if update_flow is not None:
        _update_flow_manifest(out_workspace, out_workspace / update_flow, model_rel, manifest_path, all_modules)

    out = {
        'schema': 'fsa-campaign-assemble-v1',
        'campaign': str(campaign_dir),
        'workspace': str(out_workspace),
        'manifest': str(manifest_path),
        'manifest_sha256': manifest_sha,
        'modules': all_modules,
        'compile_groups': compile_groups,
    }
    if run_flow:
        if update_flow is None or flow_out is None:
            raise ValueError('--run-flow requires both --update-flow and --flow-out')
        flow_file = (out_workspace / update_flow).resolve()
        lean_resolved = shutil.which(str(lean)) or str(Path(lean).resolve())
        prev_lean = os.environ.get('FSA_LEAN')
        os.environ['FSA_LEAN'] = lean_resolved
        try:
            flow_pin = file_sha(flow_file)
            run_res = run_pipeline(flow_file, out_workspace, Path(flow_out), expected_task_sha256=flow_pin)
            ver_res = verify_pipeline(Path(flow_out), out_workspace, expected_task_sha256=flow_pin)
        finally:
            if prev_lean is None:
                os.environ.pop('FSA_LEAN', None)
            else:
                os.environ['FSA_LEAN'] = prev_lean
        out['flow_assessment'] = run_res['assessment']
        out['flow_verify'] = ver_res['status']
    return out


def main(argv=None):
    p = argparse.ArgumentParser(prog='formal-spec-agent campaign', description=__doc__)
    sub = p.add_subparsers(dest='subcmd', required=True)

    p_init = sub.add_parser('init')
    p_init.add_argument('--workspace', type=Path, required=True)
    p_init.add_argument('--model', type=Path, required=True)
    p_init.add_argument('--campaign', type=Path, required=True)
    p_init.add_argument('--lean', default=os.environ.get('FSA_LEAN', 'lean'))
    p_init.add_argument('--skip-precompile', action='store_true')
    p_init.add_argument('--shard-size', type=int, default=8)
    p_init.add_argument('--max-attempts', type=int, default=5)
    p_init.add_argument('--cache-dir', type=Path)

    p_status = sub.add_parser('status')
    p_status.add_argument('--campaign', type=Path, required=True)

    p_claim = sub.add_parser('claim')
    p_claim.add_argument('--campaign', type=Path, required=True)
    p_claim.add_argument('--worker', required=True)
    p_claim.add_argument('--unit')
    p_claim.add_argument('--lease-seconds', type=int, default=600)

    p_rel = sub.add_parser('release')
    p_rel.add_argument('--campaign', type=Path, required=True)
    p_rel.add_argument('--unit', required=True)
    p_rel.add_argument('--worker')

    p_sub = sub.add_parser('submit')
    p_sub.add_argument('--campaign', type=Path, required=True)
    p_sub.add_argument('--unit', required=True)
    p_sub.add_argument('--source', type=Path, required=True)
    p_sub.add_argument('--lean', default=os.environ.get('FSA_LEAN', 'lean'))
    p_sub.add_argument('--worker')
    p_sub.add_argument('--lease-token')

    p_run = sub.add_parser('run-workers')
    p_run.add_argument('--campaign', type=Path, required=True)
    p_run.add_argument('--lean', default=os.environ.get('FSA_LEAN', 'lean'))
    p_run.add_argument('--concurrency', type=int, default=4)
    p_run.add_argument('--backend', choices=('command', 'provider'), required=True)
    p_run.add_argument('--cmd')
    p_run.add_argument('--provider', choices=tuple(PROVIDERS), default=DEFAULT_PROVIDER)
    p_run.add_argument('--model')
    p_run.add_argument('--ledger', type=Path)
    p_run.add_argument('--credential-file', type=Path)
    p_run.add_argument('--max-calls', type=int, default=24)
    p_run.add_argument('--max-tokens', type=int, default=8192)

    p_asm = sub.add_parser('assemble')
    p_asm.add_argument('--campaign', type=Path, required=True)
    p_asm.add_argument('--out-workspace', type=Path, required=True)
    p_asm.add_argument('--lean-dir', default='lean')
    p_asm.add_argument('--update-flow')
    p_asm.add_argument('--run-flow', action='store_true')
    p_asm.add_argument('--flow-out', type=Path)
    p_asm.add_argument('--lean', default=os.environ.get('FSA_LEAN', 'lean'))

    a = p.parse_args(argv)
    try:
        if a.subcmd == 'init':
            res = init_campaign(a.workspace, a.model, a.campaign, lean=a.lean,
                                skip_precompile=a.skip_precompile, shard_size=a.shard_size,
                                max_attempts=a.max_attempts, cache_dir=a.cache_dir)
        elif a.subcmd == 'status':
            res = status_campaign(a.campaign)
        elif a.subcmd == 'claim':
            res = claim_unit(a.campaign, a.worker, unit_id=a.unit, lease_seconds=a.lease_seconds)
            if res is None:
                print(json.dumps({'status': 'no_ready_units'}))
                return 3
        elif a.subcmd == 'release':
            res = release_unit(a.campaign, a.unit, worker_id=a.worker)
        elif a.subcmd == 'submit':
            res = submit_unit(a.campaign, a.unit, a.source, lean=a.lean,
                              worker_id=a.worker, lease_token=a.lease_token)
            print(json.dumps(res))
            return 0 if res['status'] == 'verified' else 1
        elif a.subcmd == 'run-workers':
            res = run_workers(a.campaign, lean=a.lean, concurrency=a.concurrency, backend=a.backend,
                              cmd_template=a.cmd, provider_name=a.provider, provider_model=a.model,
                              ledger=a.ledger, credential_file=a.credential_file,
                              max_calls=a.max_calls, max_tokens=a.max_tokens)
            print(json.dumps(res))
            return 0 if res['ready_to_assemble'] else 1
        else:
            res = assemble_campaign(a.campaign, a.out_workspace, lean_dir_rel=a.lean_dir,
                                    update_flow=a.update_flow, run_flow=a.run_flow,
                                    flow_out=a.flow_out, lean=a.lean)
            print(json.dumps(res))
            if a.run_flow and (res.get('flow_assessment') != 'verified_event_slice'
                               or res.get('flow_verify') != 'retained_evidence_consistent'):
                return 1
            return 0
        print(json.dumps(res))
        return 0
    except (ValueError, FileNotFoundError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print(json.dumps({'status': 'rejected', 'error_type': type(error).__name__, 'reason': str(error)}), file=sys.stderr)
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
