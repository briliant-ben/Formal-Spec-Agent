"""All-rule timer-free typed contracts derived only from authoritative IR data."""
import hashlib
import json
from pathlib import Path

from protocol_lab.ir import load, model_files
from . import lean_backend as gate
from .lean_machine import MachineView
from .lean_typed import KINDS, literal

HERE = Path(__file__).resolve().parent
TM = 'FormalSpecAgent.TypedMachine.'
TC = 'FormalSpecAgent.TypedContracts.'
MODULES = ['Foundation', 'ValueOps', 'TypedIR', 'TypedMachine', 'TypedContracts',
           'MachineObserve', 'StoreFacts']
SCOPE = ('All typed raw-rule preservation before invariant filtering, initial validity, '
         'guard disjointness, complete declared-state/external-event coverage and '
         'enabling/exact literal contracts for the timer-free atomic fragment. '
         'Not timers, reachability, native arithmetic/memory/compiler or specification correctness.')


class TypedEfsmView(MachineView):
    def __init__(self, model):
        super().__init__(model)
        if (model['timers'] or model.get('clocks') or model['scope'].get('terminal_states')
                or any(e['origin'] == 'timer' for e in model['events'].values())
                or any(set(a) not in ({'set'}, {'emit'}) for r in model['transitions'] for a in r['actions'])):
            raise ValueError('Typed EFSM gate requires timer-free set/emit atomic rules without terminal states')

    def source(self):
        source = super().source().replace('import MachineObserve\n',
            'import TypedContracts\nimport MachineObserve\nimport StoreFacts\n', 1)
        for name, left, right in [
            ('rules', 'model.rules', '['+', '.join('rule_'+str(i) for i in range(len(self.m['transitions'])))+']'),
            ('invariants', 'model.invariants', '['+', '.join(self.expr('invariant_'+str(i)) for i in range(len(self.m['invariants'])))+']'),
            ('external_events', 'model.externalEvents', '['+', '.join(str(i) for i in range(len(self.events)))+']')]:
            source += '\ntheorem model_'+name+' : '+left+' = '+right+' := rfl\n'
        for i,rule in enumerate(self.m['transitions']):
            for field,value in [('id',i),('source',self.v.states.index(rule['from'])),('event',self.events.index(rule['event']))]:
                source += '\ntheorem rule_'+field+'_'+str(i)+' : rule_'+str(i)+'.'+field+' = '+str(value)+' := rfl\n'
            for j,other in enumerate(self.m['transitions']):
                if (i != j and rule['event'] == other['event']
                        and other['guard'] == {'op':'not','args':[rule['guard']]}):
                    source += '\ntheorem guard_not_'+str(i)+'_'+str(j)+' (s : '+TM+'Snapshot) (f : FormalSpecAgent.TypedIR.Values) : '+TM+'eval s f rule_'+str(j)+'.guard = !('+TM+'eval s f rule_'+str(i)+'.guard) := rfl\n'
        return source

    def transition(self, row):
        if (type(row) is not dict or set(row) != {'rule', 'event', 'at_ms', 'after', 'emitted'}
                or row['rule'] not in [r['id'] for r in self.m['transitions']]
                or type(row['event']) is not dict or set(row['event']) != {'name', 'fields'}
                or row['event']['name'] not in self.events or type(row['emitted']) is not list
                or len(row['emitted']) > 64):
            raise ValueError('Invalid complete typed transition oracle')
        ri = next(i for i, r in enumerate(self.m['transitions']) if r['id'] == row['rule'])
        event = row['event']; schema = self.m['events'][event['name']]['fields']
        if type(event['fields']) is not dict or set(event['fields']) != set(schema) or type(row['at_ms']) is not int:
            raise ValueError('Complete typed input fields and integer trace clock required')
        fields = self.v.values(event['fields'], schema)
        after = self.snapshot(row['after'])
        if row['after']['timers'] or row['after']['now_ms'] != row['at_ms']:
            raise ValueError('Timer-free transition clock/oracle differs')
        emitters = [a['emit'] for a in self.m['transitions'][ri]['actions'] if 'emit' in a]
        messages = []
        for j, message in enumerate(row['emitted']):
            if (type(message) is not dict or set(message) != {'message', 'fields'}
                    or message['message'] not in self.messages or type(message['fields']) is not dict):
                raise ValueError('Invalid frozen typed message')
            ms = self.m['messages'][message['message']]['fields']
            if set(message['fields']) != set(ms):
                raise ValueError('Complete frozen typed message fields required')
            order = list(emitters[j]['fields']) if j < len(emitters) and set(emitters[j]['fields']) == set(ms) else list(ms)
            values = ['⟨'+str(list(ms).index(n))+', .'+KINDS[ms[n]]+', '+literal(message['fields'][n], ms[n])+'⟩' for n in order]
            messages.append('({ name := '+str(self.messages.index(message['message']))+', fields := ['+', '.join(values)+'] } : '+TM+'Message)')
        return '({ after := '+after+', rule := '+str(ri)+', event := '+str(self.events.index(event['name']))+', fields := '+fields+', emitted := ['+', '.join(messages)+'] } : '+TM+'Transition)'


def prepare(task_file, workspace, task_sha256, *, draft=False):
    root = Path(workspace).resolve(); task_file = Path(task_file).resolve()
    if not task_file.is_relative_to(root) or gate.sha(task_file) != task_sha256:
        raise ValueError('Typed EFSM task outside workspace or pin differs')
    t = json.loads(task_file.read_text())
    keys = {'schema','id','model','model_sha256','cases','cases_sha256','sources','witnesses',
            'lean_version','semantics_sha256','adapter_sha256','approved_sha256'}
    if (set(t) != keys or t['schema'] != 'fsa-lean-typed-efsm-task-v1'
            or t['lean_version'] != gate.VERSION or type(t['id']) is not str or not gate.NAME.fullmatch(t['id'])):
        raise ValueError('Invalid typed EFSM task schema/version')
    if (type(t['semantics_sha256']) is not dict or set(t['semantics_sha256']) != set(MODULES)
            or any(gate.sha(HERE/('lean/'+n+'.lean')) != t['semantics_sha256'][n] for n in MODULES)
            or gate.sha(Path(__file__).resolve()) != t['adapter_sha256']):
        raise ValueError('Typed EFSM semantics/adapter approval epoch differs')
    mf = gate.inside(root,t['model']); cf = gate.inside(root,t['cases']); chain = model_files(mf)
    if (gate.sha(mf) != t['model_sha256'] or gate.sha(cf) != t['cases_sha256']
            or any(not p.is_relative_to(root) for p in chain)):
        raise ValueError('Typed EFSM model/case path or pin differs')
    paths = [task_file,*chain,cf]; pinned = set()
    if type(t['sources']) is not list or not t['sources']:
        raise ValueError('Typed EFSM pinned sources required')
    for item in t['sources']:
        if type(item) is not dict or set(item) != {'path','sha256'}:
            raise ValueError('Invalid typed EFSM source pin')
        p = gate.inside(root,item['path'])
        if gate.sha(p) != item['sha256']: raise ValueError('Typed EFSM source digest differs')
        paths.append(p); pinned.add(p)
    if not set(chain[1:]) <= pinned: raise ValueError('Typed EFSM model bases must be pinned')
    frozen = {p:gate.sha(p) for p in paths}
    view = TypedEfsmView(load(mf)); m = view.m
    source = view.source()
    initial = dict(state=m['initial_state'], now_ms=0,
                   variables={n:v['initial'] for n,v in m['variables'].items()}, timers={})
    source += '\ndef initial : '+TM+'Snapshot := '+view.snapshot(initial)+'\n'
    goals = {'initial_valid':TC+'InitialValid model initial'}
    for i in range(len(m['transitions'])): goals['preserve_'+str(i)] = TC+'RulePreserves model rule_'+str(i)
    goals['guards_disjoint'] = TC+'GuardsDisjoint model'
    goals['coverage'] = TC+'Covers model ['+', '.join(str(i) for i in range(len(m['states'])))+']'
    cases = json.loads(cf.read_text())
    if type(cases) is not list or not 1 <= len(cases) <= 128: raise ValueError('Typed EFSM frozen cases required')
    seeds = {}; literals = {}; count = 0
    for i,c in enumerate(cases):
        if (type(c) is not dict or set(c) != {'id','initial','steps'} or type(c['id']) is not str
                or c['id'] in {k[0] for k in seeds} or type(c['steps']) is not list or not 1 <= len(c['steps']) <= 128
                or type(c['initial']) is not dict or c['initial'].get('timers') != {}):
            raise ValueError('Invalid timer-free typed case')
        before = 'initial_'+str(i); previous = c['initial']
        source += '\ndef '+before+' : '+TM+'Snapshot := '+view.snapshot(previous)+'\n'
        goals['context_valid_'+str(i)] = TM+'invariantsHold model '+before+' = true'
        for j,step in enumerate(c['steps']):
            if type(step) is not dict or set(step) != {'kind','event','fields','at_ms','expected'} or step['kind'] != 'dispatch':
                raise ValueError('Typed EFSM accepts explicit external dispatch cases only')
            cmd = {k:v for k,v in step.items() if k != 'expected'}; cmd['kind'] = 'external'
            name = str(i)+'_'+str(j); result = 'result_'+name
            source += '\ndef '+result+' := '+view.command(cmd,before)+'\n'
            e = step['expected']
            if type(e) is not dict: raise ValueError('Frozen typed outcome required')
            if set(e) == {'status','fault'} and e['status'] == 'error':
                view.expected(e,before,cmd)
                full = '.error .'+e['fault']; row = None
            else:
                if (set(e) != {'status','after','trace'} or e['status'] != 'ok' or type(e['trace']) is not list
                        or len(e['trace']) != 1): raise ValueError('Exactly one typed transition expected without timers')
                row = e['trace'][0]
                if type(row) is not dict or set(row) != {'rule','event','at_ms','after','emitted'}:
                    raise ValueError('Complete typed transition trace required')
                if row['after'] != e['after'] or row['at_ms'] != step['at_ms'] or row['event'] != dict(name=step['event'],fields=step['fields']):
                    raise ValueError('Frozen typed trace/after/input differs')
                full = '.ok '+view.transition(row)
            literals['execution_'+name] = result+' = '+full
            if (c['id'],j) in seeds: raise ValueError('Duplicate typed case step')
            seeds[(c['id'],j)] = (dict(previous,now_ms=step['at_ms']),cmd,row)
            if row is not None: previous = e['after']
            source += '\ndef after_'+name+' : '+TM+'Snapshot := '+TM+'rollback '+before+' '+result+'\n'
            before = 'after_'+name; count += 1
    if count > 512: raise ValueError('Typed EFSM literal resource limit exceeded')
    witnesses = t['witnesses']; by_rule = {}
    if type(witnesses) is not list or len(witnesses) != len(m['transitions']): raise ValueError('Exactly one enabling witness per typed rule required')
    for witness in witnesses:
        if (type(witness) is not dict or set(witness) != {'rule','case','step'} or type(witness['rule']) is not str
                or witness['rule'] in by_rule or type(witness['case']) is not str or type(witness['step']) is not int
                or (witness['case'],witness['step']) not in seeds): raise ValueError('Invalid/duplicate typed enabling witness')
        by_rule[witness['rule']] = seeds[(witness['case'],witness['step'])]
    if set(by_rule) != {r['id'] for r in m['transitions']}: raise ValueError('Typed enabling witness/rule coverage differs')
    for i,rule in enumerate(m['transitions']):
        context,cmd,row = by_rule[rule['id']]
        if row is None or row['rule'] != rule['id'] or cmd['event'] != rule['event']:
            raise ValueError('Typed enabling witness must select the declared rule/event successfully')
        fields = view.v.values(cmd['fields'],m['events'][cmd['event']]['fields'])
        goals['live_'+str(i)] = TC+'Enables model rule_'+str(i)+' '+view.snapshot(context)+' '+fields+' '+view.transition(row)
    goals.update(literals)
    source += '\n\n'.join('def '+n+' : Prop :=\n  '+p for n,p in goals.items())+'\n\nend Approved\n'
    if not draft and hashlib.sha256(source.encode()).hexdigest() != t['approved_sha256']:
        raise ValueError('Typed EFSM statements differ from frozen approval')
    if any(gate.sha(p) != h for p,h in frozen.items()): raise ValueError('Typed EFSM approved inputs changed during rendering')
    inputs = {'workspace/'+str(p.relative_to(root)):h for p,h in frozen.items()}
    for p in [Path(__file__).resolve(),HERE/'lean_machine.py',HERE/'lean_typed.py',HERE/'lean_backend.py',HERE/'lean/lean-toolchain',
              *(HERE/('lean/'+n+'.lean') for n in MODULES)]: inputs['tool/'+str(p.relative_to(HERE))] = gate.sha(p)
    inputs['ir_checker'] = gate.sha(HERE.parent/'protocol_lab/ir.py')
    return source,list(goals),inputs
