"""Check reviewed Lean sources against the scheduled semantics of pinned Protocol IR."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

from protocol_lab.ir import load, model_files
from protocol_lab.json_values import same_value

from . import lean_backend as gate
from .lean_timed_contracts import render

MODULES = (
    'Foundation', 'ValueOps', 'SequenceFacts', 'OctetFacts', 'TypedIR', 'OctetBounds',
    'TypedMachine', 'TypedContracts', 'TypedFiringContracts', 'TimerRank', 'TimerMinimum',
    'ScheduledPreservation', 'TimerDomain', 'TimerEffects', 'TimerProgress', 'BatchMachine',
    'BatchReplay', 'BatchPreservation', 'TimedSelection', 'BatchTotality', 'StoreFacts',
    'MachineObserve', 'BatchObserve', 'TimedObligations', 'GuardDiscriminators',
    'InvariantFootprint', 'ResetPreservation', 'TimerInvariantFacts', 'ExprRewrite',
    'EffectFootprint', 'GuardedSuffix', 'EffectConditions',
)
SCHEMA = 'fsa-lean-timed-proof-manifest-v1'
V2_SCHEMA = 'fsa-lean-timed-proof-manifest-v2'
V2_RESULT_SCHEMA = 'fsa-lean-timed-check-result-v2'
CHECKED = 'checked_timed_dispatch_contract'
RESULT_SCHEMA = 'fsa-lean-timed-check-result-v1'
SCOPE = 'Declared IR invariant preservation and timed dispatch from admitted states, including uncovered rollback.'
CLAIMS = ('initial', 'timers', 'preservation', 'advance', 'dispatch')
AUDIT = '''import TimedProof

namespace TimedAudit
open Approved FormalSpecAgent TypedIR TypedMachine BatchMachine BatchTotality
open TimedObligations TypedFiringContracts BatchPreservation

theorem initial : Admitted model declaredStates declaredTimers Approved.initial :=
  TimedProof.initial

theorem timers : TimerContracts model declaredStates declaredTimers :=
  TimedProof.timers

theorem preservation :
    Each (fun p => FiringPreserves model p.1 p.2) (rawChecks model declaredTimers) :=
  TimedProof.preservation

theorem advance (s : Snapshot) (limit : Int)
    (admitted : Admitted model declaredStates declaredTimers s) (bound : s.now ≤ limit) :
    ∃ batch, BatchMachine.advance model s limit = .ok batch ∧
      Drained model declaredStates declaredTimers limit batch.after ∧
      Preserved declaredTimers model batch :=
  advance_total_with_timers model declaredStates declaredTimers limit timers s admitted bound

theorem dispatch (s : Snapshot) (limit : Int)
    (admitted : Admitted model declaredStates declaredTimers s) (bound : s.now ≤ limit)
    (event : Nat) (fields : Values) (declared : event ∈ model.externalEvents) :
    ∃ prefixBatch, BatchMachine.advance model s limit = .ok prefixBatch ∧
      Drained model declaredStates declaredTimers limit prefixBatch.after ∧
      (if (enabled model prefixBatch.after event fields).isEmpty then
        BatchMachine.dispatch model s event fields limit = .error .uncovered ∧
          rollback s (BatchMachine.dispatch model s event fields limit) = s
      else ∃ batch, BatchMachine.dispatch model s event fields limit = .ok batch ∧
        Admitted model declaredStates declaredTimers batch.after ∧ batch.after.now = limit ∧
        Preserved declaredTimers model batch) :=
  dispatch_success_or_uncovered model declaredStates declaredTimers limit timers s admitted bound
    event fields declared (external_raw_from_checks model declaredTimers preservation event declared)

end TimedAudit
''' + ''.join(f'#print axioms TimedAudit.{name}\n' for name in CLAIMS)


def _pinned_bytes(path, digest):
    data = path.read_bytes()
    if hashlib.sha256(data).hexdigest() != digest:
        raise ValueError(f'Timed contract input digest differs: {path.name}')
    return data


def proof_inputs(model, manifest, manifest_sha256):
    """Read and validate the exact pinned model and module bytes."""
    model, manifest = Path(model).resolve(), Path(manifest).resolve()
    manifest_bytes = _pinned_bytes(manifest, manifest_sha256)
    policy = json.loads(manifest_bytes)
    if type(policy) is not dict or policy.get('schema') not in (SCHEMA, V2_SCHEMA):
        raise ValueError('Invalid timed proof manifest')
    expected = {'schema', 'model', 'modules'}
    if policy['schema'] == V2_SCHEMA:
        expected.add('compile_groups')
    if (set(policy) != expected or type(policy['model']) is not dict
            or type(policy['modules']) is not list):
        raise ValueError('Invalid timed proof manifest')
    model_sources = {
        name: _pinned_bytes(gate.inside(model.parent, name), digest)
        for name, digest in policy['model'].items()
    }
    if any(Path(name).as_posix() != name or '..' in Path(name).parts for name in model_sources):
        raise ValueError('Model pin must use a canonical relative path')
    if model.name not in model_sources:
        raise ValueError('Timed manifest must pin the root IR')
    proofs = {}
    for item in policy['modules']:
        if type(item) is not dict or set(item) != {'module', 'sha256'}:
            raise ValueError('Invalid reviewed Lean module entry')
        module = item['module']
        if (type(module) is not str or not re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*', module)
                or module in (*MODULES, 'Approved', 'TimedAudit') or module in proofs):
            raise ValueError('Invalid, reserved or duplicate Lean module')
        proofs[module] = _pinned_bytes(gate.inside(manifest.parent, module + '.lean'), item['sha256'])
    if not proofs or next(reversed(proofs)) != 'TimedProof':
        raise ValueError('TimedProof must be the last reviewed module')

    _reviewed_groups(policy, proofs)
    return manifest_bytes, model_sources, proofs


def _reviewed_groups(policy, proofs):
    if policy['schema'] == SCHEMA:
        return [[name] for name in proofs]
    groups = policy['compile_groups']
    if (type(groups) is not list or not groups
            or any(type(group) is not list or not 1 <= len(group) <= 2
                   or any(type(name) is not str for name in group) for group in groups)
            or [name for group in groups for name in group] != list(proofs)
            or groups[-1] != ['TimedProof']):
        raise ValueError('Compile groups must cover reviewed modules exactly in order')
    known = set(MODULES) | set(proofs) | {'Approved', 'TimedAudit'}
    ready = set(MODULES) | {'Approved'}
    for group in groups:
        for name in group:
            for line in proofs[name].decode('utf-8').splitlines():
                header = line.strip()
                if re.match(r'^(?:public\s+)?import\b', header):
                    match = re.fullmatch(r'import +([A-Za-z][A-Za-z0-9_.]*(?: +[A-Za-z][A-Za-z0-9_.]*)*)', header)
                    if not match:
                        raise ValueError('Unsupported reviewed import header for compile groups')
                    for dependency in match.group(1).split():
                        if dependency in known and dependency not in ready:
                            raise ValueError('Reviewed import needs an earlier compilation group')
        ready.update(group)
    return groups


def _schedule(manifest_bytes, proofs):
    policy = json.loads(manifest_bytes)
    groups = [[name] for name in MODULES] + [['Approved']]
    groups += _reviewed_groups(policy, proofs) + [['TimedAudit']]
    return groups


def _compile_one(tool, out, env, name):
    command = [tool, '-o', name + '.olean', name + '.lean']
    try:
        completed = subprocess.run(command, cwd=out, env=env, capture_output=True,
                                   text=True, timeout=60)
        stdout, stderr, code = completed.stdout, completed.stderr, completed.returncode
    except subprocess.TimeoutExpired as error:
        stdout = (error.stdout or b'').decode(errors='replace')
        stderr, code = 'Lean wall-clock timeout', None
    (out/f'{name}.stdout').write_text(stdout)
    (out/f'{name}.stderr').write_text(stderr)
    return dict(module=name, returncode=code,
                stdout_sha256=gate.sha(out/f'{name}.stdout'),
                stderr_sha256=gate.sha(out/f'{name}.stderr'))


def _sources(frozen_model, model_sources, proofs):
    if set(model_sources) != {p.relative_to(frozen_model.parent).as_posix() for p in model_files(frozen_model)}:
        raise ValueError('Timed manifest must pin the exact model inheritance chain')
    approved, goals = render(load(frozen_model))
    sources = {name: (gate.HERE/'lean'/f'{name}.lean').read_bytes() for name in MODULES}
    sources.update(Approved=approved.encode())
    sources.update(proofs)
    sources.update(TimedAudit=AUDIT.encode())
    return sources, goals


def _identity(manifest_sha256, model_sources, sources, goals, groups=None):
    def digests(values):
        return {name: hashlib.sha256(data).hexdigest() for name, data in values.items()}
    identity = dict(
        schema=RESULT_SCHEMA, scope=SCOPE, proof_manifest_sha256=manifest_sha256,
        model=digests(model_sources), sources=digests(sources),
        raw_firings=sum(name.startswith('raw_') for name in goals) - 1,
        conflict_groups=sum(name.startswith('conflict_') for name in goals) - 1,
        compiler_correctness_proved=False, protocol_correctness_proved=False,
    )
    if groups is not None:
        identity.update(schema=V2_RESULT_SCHEMA, compile_groups=groups)
    return identity


def check(model, manifest, manifest_sha256, out, lean='lean'):
    """Build a fresh evidence directory from source reviewed by the caller."""
    model, out = Path(model).resolve(), Path(out).resolve()
    manifest_bytes, model_sources, proofs = proof_inputs(model, manifest, manifest_sha256)
    groups = _schedule(manifest_bytes, proofs)
    grouped = json.loads(manifest_bytes)['schema'] == V2_SCHEMA
    out.mkdir()
    (out/'proof-manifest.json').write_bytes(manifest_bytes)
    ir_root = out/'ir'
    for name, data in model_sources.items():
        target = ir_root/name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
    sources, goals = _sources(ir_root/model.name, model_sources, proofs)
    for name, data in sources.items():
        path = out/f'{name}.lean'
        path.write_bytes(data)
        path.chmod(0o444)

    result = dict(_identity(manifest_sha256, model_sources, sources, goals, groups if grouped else None),
                  status='incomplete', commands=[])
    tool = shutil.which(str(lean))
    if tool is None:
        result.update(status='blocked', classification='environment')
    else:
        tool = str(Path(tool).resolve())
        version = subprocess.check_output([tool, '--version'], text=True, timeout=15).strip()
        if not re.search(r'\bversion ' + re.escape(gate.VERSION) + r'(?:,|\))', version):
            raise ValueError('Pinned Lean version required')
        result.update(lean_version=version, lean_binary_sha256=gate.sha(tool))
        env = dict(PATH=os.defpath, LEAN_PATH=str(out), LANG='C.UTF-8')
        for index, group in enumerate(groups):
            if len(group) == 1:
                receipts = [_compile_one(tool, out, env, group[0])]
            else:
                with ThreadPoolExecutor(max_workers=2) as pool:
                    receipts = list(pool.map(lambda name: _compile_one(tool, out, env, name), group))
            result['commands'].extend(receipts)
            failures = [receipt for receipt in receipts if receipt['returncode'] != 0]
            if failures:
                resource = all(gate.resource_failure(
                    receipt['returncode'], (out/(receipt['module']+'.stdout')).read_text(),
                    (out/(receipt['module']+'.stderr')).read_text()) for receipt in failures)
                result.update(status='fail', failed_module=failures[0]['module'],
                              classification='resource_unknown' if resource else 'proof_failure')
                if grouped:
                    result['failed_group'] = index
                break
        else:
            try:
                stdout = (out/'TimedAudit.stdout').read_text()
                result['axioms'] = {name: gate.read_axioms(stdout, f'TimedAudit.{name}') for name in CLAIMS}
            except ValueError as error:
                result.update(status='fail', classification='axiom_audit', reason=str(error))
            else:
                result.update(status=CHECKED)
    if (gate.sha(out/'proof-manifest.json') != manifest_sha256
            or any(gate.sha(ir_root/name) != digest for name, digest in result['model'].items())
            or any(gate.sha(out/f'{name}.lean') != digest for name, digest in result['sources'].items())):
        result.update(status='invalidated_inputs', classification='evidence_changed')
    gate.write(out/'result.json', result)
    return result


def inspect(bundle, model, manifest, manifest_sha256, *, require_pass=True):
    """Validate retained identity, command coverage and axioms without executing Lean."""
    bundle = Path(bundle).resolve()
    manifest_bytes, model_sources, proofs = proof_inputs(model, manifest, manifest_sha256)
    if (bundle/'proof-manifest.json').read_bytes() != manifest_bytes:
        raise ValueError('Retained timed proof manifest differs')
    for name, data in model_sources.items():
        if (bundle/'ir'/name).read_bytes() != data:
            raise ValueError('Retained timed model differs')
    sources, goals = _sources(bundle/'ir'/Path(model).name, model_sources, proofs)
    grouped = json.loads(manifest_bytes)['schema'] == V2_SCHEMA
    groups = _schedule(manifest_bytes, proofs)
    identity = _identity(manifest_sha256, model_sources, sources, goals, groups if grouped else None)
    report = json.loads((bundle/'result.json').read_text())
    if type(report) is not dict or any(not same_value(report.get(name), expected)
                                       for name, expected in identity.items()):
        raise ValueError('Retained timed claim or input identity differs')
    for name, data in sources.items():
        if (bundle/f'{name}.lean').read_bytes() != data:
            raise ValueError('Retained timed source differs')
    commands = report.get('commands')
    if (type(commands) is not list or any(type(c) is not dict
            or set(c) != {'module', 'returncode', 'stdout_sha256', 'stderr_sha256'}
            or (c['returncode'] is not None and type(c['returncode']) is not int)
            for c in commands)):
        raise ValueError('Invalid timed compiler receipt types')
    if not commands or [c['module'] for c in commands] != list(sources)[:len(commands)]:
        raise ValueError('Timed compilation coverage or order differs')
    for receipt in commands:
        name = receipt['module']
        if (gate.sha(bundle/f'{name}.stdout') != receipt['stdout_sha256']
                or gate.sha(bundle/f'{name}.stderr') != receipt['stderr_sha256']):
            raise ValueError('Timed compiler log differs')
    stops = []
    count = 0
    for group in groups:
        count += len(group)
        stops.append(count)
    if len(commands) not in stops:
        raise ValueError('Incomplete compilation group receipt')
    completed_group = stops.index(len(commands))
    final_start = 0 if completed_group == 0 else stops[completed_group - 1]
    if any(c['returncode'] != 0 for c in commands[:final_start]):
        raise ValueError('Timed compilation continued after a failed group')
    failures = [c for c in commands[final_start:] if c['returncode'] != 0]
    if report['status'] == CHECKED:
        if len(commands) != len(sources) or failures:
            raise ValueError('Incomplete timed obligations falsely promoted')
        if grouped and any(key in report for key in ('failed_module', 'failed_group', 'classification')):
            raise ValueError('Successful timed report includes failed-group metadata')
        stdout = (bundle/'TimedAudit.stdout').read_text()
        if report['axioms'] != {name: gate.read_axioms(stdout, f'TimedAudit.{name}') for name in CLAIMS}:
            raise ValueError('Timed axiom audit differs')
    else:
        if (require_pass or not failures or report['failed_module'] != failures[0]['module']
                or report.get('classification') != 'resource_unknown' or report['status'] != 'fail'
                or (grouped and (type(report.get('failed_group')) is not int
                                 or report['failed_group'] != completed_group))
                or not all(gate.resource_failure(c['returncode'],
                    (bundle/(c['module']+'.stdout')).read_text(),
                    (bundle/(c['module']+'.stderr')).read_text()) for c in failures)):
            raise ValueError('Timed contract result did not pass')
    return report


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('model', type=Path)
    parser.add_argument('--proof-manifest', type=Path, required=True)
    parser.add_argument('--proof-sha256', required=True,
                        help='Digest of the caller-reviewed manifest for executable Lean source')
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--lean', default='lean')
    args = parser.parse_args(argv)
    try:
        result = check(args.model, args.proof_manifest, args.proof_sha256, args.out, args.lean)
    except (ValueError, TypeError, KeyError, OSError, subprocess.SubprocessError) as error:
        print(json.dumps(dict(status='rejected', reason=str(error))), file=sys.stderr)
        return 2
    print(json.dumps(result))
    return 0 if result['status'] == CHECKED else 1
