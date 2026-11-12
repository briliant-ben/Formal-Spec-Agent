"""Exact default-initial, depth-one contracts, with replayable query journals.

UNSAT relies on Z3 and the independent Encoding translation. Verification checks
current-code derivation and evidence consistency, not execution attestation: a
coherently forged set of solver answers needs external provenance/certificates.
No deeper/all-state, wire, compiler or English-spec correctness is claimed.
"""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

import z3
from .ir import validate
from .symbolic import Encoding, model_hash, replay

SCHEMA = 'initial-step-contracts-v1'
PASS = 'initial_step_contracts_pass'
UNRESOLVED = 'unresolved_or_counterexample_unreplayed'
SCOPE = 'default initialized depth1; full typed defined transitions; not all-state/deeper/wire/compiler/spec proof'
SOURCE_NAMES = ('initial_step.py', 'initial_plan.py', 'initial_units.py', 'initial_overlap.py', 'symbolic.py', 'ir.py')


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def write(path, value):
    path.write_text(json.dumps(value, sort_keys=True, indent=2) + '\n')


def supported(model):
    validate(model)
    if (model['ir_version'] != '0.6' or model['semantics'] != 'flat-efsm-atomic-ordered-v1'
            or model['scope']['terminal_states'] or not model['transitions'] or not model['invariants']):
        raise ValueError('Unsupported initialized one-step scope')


def sources():
    root = Path(__file__).resolve().parent
    return {name: digest((root / name).read_bytes()) for name in SOURCE_NAMES}


def budget(value):
    if type(value) is not int or not 100 <= value <= 60000:
        raise ValueError('Solver budget must be integer 100..60000ms')
    return value


def render(model):
    """Never import or run stored job code. Reset Z3 AST naming in a fresh process."""
    root = Path(__file__).resolve().parents[1]
    env = dict(os.environ, PYTHONPATH=str(root), PYTHONDONTWRITEBYTECODE='1')
    result = subprocess.run([sys.executable, '-m', 'protocol_lab.initial_step', '--render'],
                            input=json.dumps(model, sort_keys=True), text=True, capture_output=True,
                            cwd=root, env=env, timeout=120, check=True)
    plan = json.loads(result.stdout)
    if (plan['schema'] != 'initial-step-plan-v1' or plan['depth'] != 1
            or plan['default_initials'] != [] or plan['model_semantic_sha256'] != model_hash(model)):
        raise ValueError('Plan identity differs')
    return plan


def manifest(plan, model):
    rows = [('choice_cover', 'choice_cover', 'plain', plan['choice_cover'])]
    safety = plan['safety']
    if [r['choice'] for r in safety] != list(range(len(model['transitions']))) + [-1, -2]:
        raise ValueError('Choice partition omitted or reordered')
    rows += [('safety_' + str(r['choice']), 'safety', 'exact', r['smt2']) for r in safety]
    leaves = plan['overlap']['queries']
    if [r['index'] for r in leaves] != list(range(plan['overlap']['leaf_count'])):
        raise ValueError('Overlap obligations omitted or reordered')
    rows += [('overlap_' + str(r['index']), 'overlap', 'plain', r['smt2']) for r in leaves]
    rows += [('nonvac_witness', 'nonvac', 'sample', plan['nonvac_smt2'])]
    queries = [dict(id=i, role=role, solver_policy=policy, file='queries/' + i + '.smt2',
                    sha256=digest(smt.encode()), smt2=smt) for i, role, policy, smt in rows]
    overlap_metadata = {"overlap_" + str(r['index']): r for r in leaves}
    for q in queries:
        if q['role'] == 'overlap':
            q.update({k: overlap_metadata[q['id']][k] for k in ('derivation', 'source_leaf_sha256')})
    roots = [dict(id=n, role=n, file='queries/' + n + '.smt2',
                  sha256=digest(plan[n]['smt2'].encode()), smt2=plan[n]['smt2'])
             for n in ('original_safety', 'original_overlap')]
    return queries, roots


def metadata(row):
    return {k: v for k, v in row.items() if k != 'smt2'}


def aggregate(rows):
    neg = [r for r in rows if r['role'] != 'nonvac']
    sample = rows[-1]
    matched = sample.get('reference_replay', {}).get('status') == 'match'
    counts = dict(negative_queries=len(neg),
                  negative_answers={a: sum(r['answer'] == a for r in neg) for a in ('sat', 'unsat', 'unknown')},
                  nonvac_answer=sample['answer'], nonvac_replay_match=matched)
    good = all(r['answer'] == 'unsat' for r in neg) and sample['answer'] == 'sat' and matched
    return (PASS if good else UNRESOLVED), counts


def header(model, timeout):
    return dict(schema=SCHEMA, model_semantic_sha256=model_hash(model), source_sha256=sources(),
                solver_version=z3.get_version_string(), solver_timeout_ms=timeout,
                depth=1, symbolic_initials=[], scope=SCOPE, old_UNKNOWN_unchanged=True)


def check(model, out, solver_timeout_ms=10000):
    timeout = budget(solver_timeout_ms)
    supported(model)
    if out is None:
        raise ValueError('A fresh query journal is required')
    folder = Path(out)
    if folder.is_symlink() or (folder.exists() and (not folder.is_dir() or any(folder.iterdir()))):
        raise ValueError('Fresh empty journal required')
    folder.mkdir(parents=True, exist_ok=True)
    before = header(model, timeout)
    queries, roots = manifest(render(model), model)
    (folder / 'queries').mkdir()
    # Persist ALL queries and derivation roots before the first solve.
    for q in queries + roots:
        (folder / q['file']).write_text(q['smt2'])
    rows = []
    for q in queries:
        ctx = None if q['role'] == 'nonvac' else z3.Context()
        solver = (z3.Then(z3.Tactic('solve-eqs', ctx=ctx), z3.Tactic('simplify', ctx=ctx),
                          z3.Tactic('smt', ctx=ctx)).solver()
                  if q['solver_policy'] == 'exact' else z3.Solver(ctx=ctx))
        solver.from_string(q['smt2'])
        solver.set(timeout=timeout)
        try:
            answer = solver.check()
            reason = solver.reason_unknown() if answer == z3.unknown else None
        except z3.Z3Exception as exc:
            answer, reason = z3.unknown, 'solver_exception:' + str(exc)
        row = dict(metadata(q), answer=str(answer), reason=reason, timeout_ms=timeout)
        if answer == z3.sat and q['role'] == 'nonvac':
            enc = Encoding(model, 1, [], fixed_choices=[0], solver_preprocess='none')
            row['witness'] = enc.witness(solver.model())
            row['reference_replay'] = replay(model, row['witness'])
        elif answer == z3.sat:
            row['counterexample_replay'] = 'not performed; not an accepted protocol counterexample'
        rows.append(row)
        write(folder / ('receipt_' + q['id'] + '.json'), row)
    if header(model, timeout) != before:
        raise ValueError('Sources/model changed during check')
    status, counts = aggregate(rows)
    report = dict(before, status=status, counts=counts, queries=rows,
                  original_queries=[metadata(q) for q in roots])
    write(folder / 'result.json', report)
    return report


def _verify(model, out, require_pass):
    supported(model)
    folder = Path(out)
    if folder.is_symlink() or not folder.is_dir():
        raise ValueError('Journal directory unavailable')
    # Reject links BEFORE reading any evidence, and never use report-supplied paths.
    if any(p.is_symlink() for p in folder.rglob('*')):
        raise ValueError('Symlink evidence rejected')
    report = json.loads((folder / 'result.json').read_text())
    timeout = budget(report['solver_timeout_ms'])
    expected_header = header(model, timeout)
    if set(report) != set(expected_header) | {'status', 'counts', 'queries', 'original_queries'}:
        raise ValueError('Unexpected/missing report fields')
    if any(type(report[k]) != type(v) or report[k] != v for k, v in expected_header.items()):
        raise ValueError('Source/model/solver/scope binding changed')
    queries, roots = manifest(render(model), model)
    expected_files = {'result.json'} | {q['file'] for q in queries + roots}
    expected_files |= {'receipt_' + q['id'] + '.json' for q in queries}
    actual_files = {p.relative_to(folder).as_posix() for p in folder.rglob('*') if p.is_file()}
    if expected_files != actual_files:
        raise ValueError('Missing/extra evidence')
    if report['original_queries'] != [metadata(q) for q in roots]:
        raise ValueError('Original derivation roots changed')
    rows = report['queries']
    if type(rows) is not list or [r['id'] for r in rows] != [q['id'] for q in queries]:
        raise ValueError('Obligations omitted/duplicated/reordered')
    for q in queries + roots:
        if (folder / q['file']).read_bytes() != q['smt2'].encode():
            raise ValueError('Query differs from current trusted derivation: ' + q['id'])
    for q, row in zip(queries, rows):
        receipt = json.loads((folder / ('receipt_' + q['id'] + '.json')).read_text())
        if receipt != row or any(row.get(k) != v for k, v in metadata(q).items()):
            raise ValueError('Manifest/receipt binding changed: ' + q['id'])
        if type(row['timeout_ms']) is not int or row['timeout_ms'] != timeout or row['answer'] not in ('sat', 'unsat', 'unknown'):
            raise ValueError('Invalid answer or solver budget')
        if row['answer'] == 'unknown':
            if not isinstance(row['reason'], str) or not row['reason']:
                raise ValueError('UNKNOWN reason missing')
        elif row['reason'] is not None:
            raise ValueError('Unexpected solver reason')
        expected_keys = set(metadata(q)) | {'answer', 'reason', 'timeout_ms'}
        if row['answer'] == 'sat' and q['role'] == 'nonvac':
            expected_keys |= {'witness', 'reference_replay'}
            w = row['witness']
            if (w['initial'] != {k: v['initial'] for k, v in model['variables'].items()}
                    or len(w['steps']) != 1 or w['steps'][0]['transition'] != model['transitions'][0]['id']):
                raise ValueError('Nonvacuity witness is outside its declared initial/choice scope')
            if replay(model, w) != row['reference_replay']:
                raise ValueError('Nonvacuity strict replay changed')
        elif row['answer'] == 'sat':
            expected_keys |= {'counterexample_replay'}
            if row['counterexample_replay'] != 'not performed; not an accepted protocol counterexample':
                raise ValueError('Counterexample scope changed')
        if set(row) != expected_keys:
            raise ValueError('Unexpected/missing receipt fields')
    status, counts = aggregate(rows)
    if report['status'] != status or report['counts'] != counts:
        raise ValueError('Aggregate result falsely promoted or changed')
    if require_pass and status != PASS:
        raise ValueError('Initialized contracts unresolved')
    return dict(status='verified_pass' if status == PASS else 'verified_unresolved', errors=[],
                model_semantic_sha256=model_hash(model))


def verify(model, out, require_pass=True):
    """Re-derive every query and replay the witness, without solving or archive code."""
    try:
        return _verify(model, out, require_pass)
    except (ValueError, KeyError, TypeError, OSError, IndexError, z3.Z3Exception) as exc:
        return dict(status='verification_failed', errors=[str(exc)])


if __name__ == '__main__':
    if sys.argv[1:] != ['--render']:
        raise SystemExit('Only --render is supported; check/verify are Python APIs')
    from .initial_plan import render_plan
    print(json.dumps(render_plan(json.load(sys.stdin)), sort_keys=True))
