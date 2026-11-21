"""Kernel-check timed traces against literal outcomes, including error rollback."""
import hashlib
import json
from pathlib import Path

from protocol_lab.ir import load, model_files

from . import lean_backend as gate
from .lean_batch import BatchView, MODULES, NS, OBS

SCHEMA = 'fsa-lean-timed-replay-task-v1'
SCOPE = ('Exact frozen timed dispatch and tick observations, including faults and '
         'rollback. The certificate covers the supplied trace cases.')
ADAPTER = Path(__file__).resolve()
TOOLS = (ADAPTER, gate.HERE / 'lean_batch.py', gate.HERE / 'lean_machine.py',
         gate.HERE / 'lean_typed.py')


def prepare(task_file, workspace, task_sha256, *, draft=False):
    root = Path(workspace).resolve()
    task_file = Path(task_file).resolve()
    if not task_file.is_relative_to(root) or gate.sha(task_file) != task_sha256:
        raise ValueError('Timed replay task outside workspace or digest mismatch')
    task = json.loads(task_file.read_text())
    keys = {'schema', 'id', 'model', 'oracle', 'sources', 'lean_version',
            'semantics_sha256', 'adapters_sha256', 'approved_sha256'}
    if (set(task) != keys or task['schema'] != SCHEMA or task['lean_version'] != gate.VERSION
            or type(task['id']) is not str or not gate.NAME.fullmatch(task['id'])):
        raise ValueError('Invalid timed replay task schema')
    semantics = {name: gate.sha(gate.HERE / 'lean' / (name + '.lean')) for name in MODULES}
    adapters = {path.name: gate.sha(path) for path in TOOLS}
    if task['semantics_sha256'] != semantics or task['adapters_sha256'] != adapters:
        raise ValueError('Timed replay approval epoch differs')

    def pinned_file(pin):
        if type(pin) is not dict or set(pin) != {'path', 'sha256'}:
            raise ValueError('Invalid timed replay file pin')
        path = gate.inside(root, pin['path'])
        if gate.sha(path) != pin['sha256']:
            raise ValueError('Timed replay file digest differs')
        return path

    model = pinned_file(task['model'])
    oracle = pinned_file(task['oracle'])
    if type(task['sources']) is not list or not task['sources']:
        raise ValueError('Timed replay requires pinned sources')
    sources = {pinned_file(pin) for pin in task['sources']}
    if not set(model_files(model)[1:]) <= sources:
        raise ValueError('Timed replay model bases must be pinned')

    approved, goals = render(BatchView(load(model)), json.loads(oracle.read_text()))
    if not draft and hashlib.sha256(approved.encode()).hexdigest() != task['approved_sha256']:
        raise ValueError('Frozen timed replay statements differ')
    inputs = {'workspace/' + str(path.relative_to(root)): gate.sha(path)
              for path in sorted({task_file, model, oracle, *sources})}
    inputs.update({'tool/' + name: digest for name, digest in adapters.items()})
    inputs.update({'tool/lean/' + name + '.lean': digest for name, digest in semantics.items()})
    inputs['tool/lean_backend.py'] = gate.sha(Path(gate.__file__))
    inputs['tool/lean/lean-toolchain'] = gate.sha(gate.HERE / 'lean/lean-toolchain')
    inputs['ir_checker'] = gate.sha(gate.HERE.parent / 'protocol_lab/ir.py')
    return approved, list(goals), inputs


def render(view, cases):
    if type(cases) is not list or not 1 <= len(cases) <= 128:
        raise ValueError('Frozen timed replay cases required')
    declarations = [view.source(proof_helpers=True)]
    goals = {}
    ids = set()
    count = 0
    for i, case in enumerate(cases):
        if (type(case) is not dict or set(case) != {'id', 'initial', 'steps'}
                or type(case['id']) is not str or not case['id'] or case['id'] in ids
                or type(case['steps']) is not list or not 1 <= len(case['steps']) <= 128):
            raise ValueError('Invalid timed replay case')
        ids.add(case['id'])
        count += len(case['steps'])
        if count > 512:
            raise ValueError('Timed replay step limit exceeded')
        before = f'initial_{i}'
        declarations.append(f"def {before} := {view.snapshot(case['initial'])}")
        goals[f'initial_valid_{i}'] = (
            f'FormalSpecAgent.TypedMachine.invariantsHold model {before} = true ∧ '
            f'FormalSpecAgent.TimerRank.WellTimed {before}')
        order = sorted(case['initial']['timers'])
        for j, step in enumerate(case['steps']):
            if type(step) is not dict or 'expected' not in step:
                raise ValueError('Timed replay requires an explicit oracle')
            name = f'{i}_{j}'
            command = {k: v for k, v in step.items() if k != 'expected'}
            expected = step['expected']
            result = f'result_{name}'
            declarations.append(f'def {result} := {view.command(command, before)}')
            if type(expected) is dict and expected.get('status') == 'error':
                if set(expected) != {'status', 'fault', 'after', 'trace'} or expected['trace'] != []:
                    raise ValueError('Timed replay fault requires explicit rollback state and empty trace')
                fault = {key: expected[key] for key in ('status', 'fault')}
                observation = view.expected(fault, view.snapshot(expected['after']), command)
                execution, order = view.full_expected(fault, order)
            else:
                observation = view.expected(expected, before, command)
                execution, order = view.full_expected(expected, order)
            goals[f'execution_{name}'] = f'{result} = {execution}'
            goals[f'witness_{name}'] = (
                f'{OBS}outcome schema eventSchemas {before} {result} = {observation}')
            next_state = f'after_{name}'
            declarations.append(f'def {next_state} := {NS}rollback {before} {result}')
            before = next_state
    declarations.extend(f'def {name} : Prop :=\n  {goal}' for name, goal in goals.items())
    declarations.append('end Approved\n')
    return '\n\n'.join(declarations), goals
