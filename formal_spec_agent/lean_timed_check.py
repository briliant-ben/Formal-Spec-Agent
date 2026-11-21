"""Check reviewed Lean sources against the scheduled semantics of pinned Protocol IR."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

from protocol_lab.ir import load, model_files

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
    if (type(policy) is not dict or set(policy) != {'schema', 'model', 'modules'}
            or policy['schema'] != SCHEMA or type(policy['model']) is not dict
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

    return manifest_bytes, model_sources, proofs


def _sources(frozen_model, model_sources, proofs):
    if set(model_sources) != {p.relative_to(frozen_model.parent).as_posix() for p in model_files(frozen_model)}:
        raise ValueError('Timed manifest must pin the exact model inheritance chain')
    approved, goals = render(load(frozen_model))
    sources = {name: (gate.HERE/'lean'/f'{name}.lean').read_bytes() for name in MODULES}
    sources.update(Approved=approved.encode())
    sources.update(proofs)
    sources.update(TimedAudit=AUDIT.encode())
    return sources, goals


def _identity(manifest_sha256, model_sources, sources, goals):
    def digests(values):
        return {name: hashlib.sha256(data).hexdigest() for name, data in values.items()}
    return dict(
        schema=RESULT_SCHEMA, scope=SCOPE, proof_manifest_sha256=manifest_sha256,
        model=digests(model_sources), sources=digests(sources),
        raw_firings=sum(name.startswith('raw_') for name in goals) - 1,
        conflict_groups=sum(name.startswith('conflict_') for name in goals) - 1,
        compiler_correctness_proved=False, protocol_correctness_proved=False,
    )


def check(model, manifest, manifest_sha256, out, lean='lean'):
    """Build a fresh evidence directory from source reviewed by the caller."""
    model, out = Path(model).resolve(), Path(out).resolve()
    manifest_bytes, model_sources, proofs = proof_inputs(model, manifest, manifest_sha256)
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

    result = dict(_identity(manifest_sha256, model_sources, sources, goals),
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
        for name in sources:
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
            result['commands'].append(dict(module=name, returncode=code,
                                           stdout_sha256=gate.sha(out/f'{name}.stdout'),
                                           stderr_sha256=gate.sha(out/f'{name}.stderr')))
            if code != 0:
                result.update(status='fail', failed_module=name,
                              classification='resource_unknown' if gate.resource_failure(
                                  code, stdout, stderr) else 'proof_failure')
                break
        else:
            try:
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
    identity = _identity(manifest_sha256, model_sources, sources, goals)
    report = json.loads((bundle/'result.json').read_text())
    if any(report.get(name) != expected for name, expected in identity.items()):
        raise ValueError('Retained timed claim or input identity differs')
    for name, data in sources.items():
        if (bundle/f'{name}.lean').read_bytes() != data:
            raise ValueError('Retained timed source differs')
    commands = report['commands']
    if not commands or [c['module'] for c in commands] != list(sources)[:len(commands)]:
        raise ValueError('Timed compilation coverage or order differs')
    for receipt in commands:
        name = receipt['module']
        if (gate.sha(bundle/f'{name}.stdout') != receipt['stdout_sha256']
                or gate.sha(bundle/f'{name}.stderr') != receipt['stderr_sha256']):
            raise ValueError('Timed compiler log differs')
    if any(c['returncode'] != 0 for c in commands[:-1]):
        raise ValueError('Timed compilation continued after a failure')
    if report['status'] == CHECKED:
        if len(commands) != len(sources) or commands[-1]['returncode'] != 0:
            raise ValueError('Incomplete timed obligations falsely promoted')
        stdout = (bundle/'TimedAudit.stdout').read_text()
        if report['axioms'] != {name: gate.read_axioms(stdout, f'TimedAudit.{name}') for name in CLAIMS}:
            raise ValueError('Timed axiom audit differs')
    else:
        name = commands[-1]['module']
        if (require_pass or report.get('failed_module') != name
                or report.get('classification') != 'resource_unknown' or report['status'] != 'fail'
                or not gate.resource_failure(commands[-1]['returncode'],
                                             (bundle/f'{name}.stdout').read_text(),
                                             (bundle/f'{name}.stderr').read_text())):
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
