"""Typed ordered actions and explicitly scheduled microsteps, derived from IR."""
import hashlib
import json
from pathlib import Path

from protocol_lab.ir import load, model_files, value_ok
from . import lean_backend as gate
from .lean_typed import View, KINDS, literal

HERE=Path(__file__).resolve().parent
NS='FormalSpecAgent.TypedMachine.'
SCOPE=('Typed ordered actions and explicit scheduled microstep literal contracts. '
       'Not batch dispatch/tick, universal rule preservation, full EFSM safety, '
       'native overflow/compiler or specification correctness.')
MODULES=['Foundation','ValueOps','TypedIR','TypedMachine','MachineObserve']


class MachineView:
    def __init__(self,model):
        if any(set(t)!={'event'}for t in model['timers'].values()):raise ValueError('Unsupported typed machine timer fields')
        self.m=model;self.v=View(model).build();self.timers=sorted(model['timers']);self.events=list(model['events']);self.messages=list(model['messages'])
        if any(t not in KINDS for x in model['messages'].values()for t in x['fields'].values()):raise ValueError('Unsupported machine message type')
        if any(set(a)not in ({'set'},{'emit'},{'arm'},{'cancel'})for r in model['transitions']for a in r['actions']):raise ValueError('Unsupported typed machine action')
        # Timer expression indices must use canonical name order too. Expr.state
        # indices remain model order. Rebuild the DAG with the same timer order.
        self.v=View(model);self.v.timers=self.timers;self.v.build()
    def expr(self,name):return 'e'+str(self.v.roots[name]['node'])
    def source(self):
        s=self.v.source().replace('import TypedIR\n','import MachineObserve\n',1)
        for i,r in enumerate(self.m['transitions']):
            actions=[]
            for j,a in enumerate(r['actions']):
                tag,x=next(iter(a.items()));name='action_'+str(i)+'_'+str(j)
                if tag=='set':
                    k=self.m['variables'][x['var']]['type'];actions.append(NS+'Action.assign .'+KINDS[k]+' '+str(self.v.variables.index(x['var']))+' '+self.expr(name))
                elif tag=='emit':
                    fs=[]
                    for f,e in x['fields'].items():
                        schema=self.m['messages'][x['message']]['fields'];idx=list(x['fields']).index(f);k=schema[f]
                        fs.append('⟨'+str(list(schema).index(f))+', .'+KINDS[k]+', '+self.expr(name+'_'+str(idx))+'⟩')
                    actions.append(NS+'Action.emit '+str(self.messages.index(x['message']))+' ['+', '.join(fs)+']')
                elif tag=='arm':actions.append(NS+'Action.arm '+str(self.timers.index(x['timer']))+' '+self.expr(name))
                elif tag=='cancel':actions.append(NS+'Action.cancel '+str(self.timers.index(x)))
            s+='\ndef rule_'+str(i)+' : '+NS+'Rule :=\n  { id := '+str(i)+', source := '+str(self.v.states.index(r['from']))+', target := '+str(self.v.states.index(r['to']))+', event := '+str(self.events.index(r['event']))+', guard := '+self.expr('guard_'+str(i))+', actions := ['+', '.join(actions)+'] }\n'
        schema='['+', '.join('(.'+KINDS[v['type']]+', '+str(i)+')'for i,v in enumerate(self.m['variables'].values()))+']'
        s+='\ndef schema : List (FormalSpecAgent.TypedIR.Kind × Nat) := '+schema+'\n'
        inv='['+', '.join(self.expr('invariant_'+str(i))for i in range(len(self.m['invariants'])))+']'
        timers=''.join('if n = '+str(i)+' then '+str(self.events.index(self.m['timers'][n]['event']))+' else 'for i,n in enumerate(self.timers))
        ext='['+', '.join(str(i)for i,n in enumerate(self.events)if self.m['events'][n]['origin']!='timer')+']'
        s+='\ndef model : '+NS+'Model :=\n  { rules := ['+', '.join('rule_'+str(i)for i in range(len(self.m['transitions'])))+'], invariants := '+inv+', timerEvents := fun n => '+timers+'0, externalEvents := '+ext+' }\n'
        return s
    def snapshot(self,s):
        if type(s)is not dict or set(s)!={'state','now_ms','variables','timers'}or s['state']not in self.v.states or type(s['now_ms'])is not int or s['now_ms']<0:raise ValueError('Invalid machine snapshot/state/time')
        if type(s['variables'])is not dict or set(s['variables'])!=set(self.m['variables']):raise ValueError('Complete typed snapshot variables required')
        if type(s['timers'])is not dict or not set(s['timers'])<=set(self.timers)or any(type(t)is not int or t<s['now_ms']for t in s['timers'].values()):raise ValueError('Invalid machine timer snapshot')
        store=self.v.values(s['variables'],{n:v['type']for n,v in self.m['variables'].items()})
        timers='['+', '.join('⟨'+str(self.timers.index(n))+', '+gate.number(s['timers'][n])+'⟩'for n in self.timers if n in s['timers'])+']'
        return '({ values := '+store+', state := '+str(self.v.states.index(s['state']))+', now := '+gate.number(s['now_ms'])+', timers := '+timers+' } : '+NS+'Snapshot)'
    def command(self,c,snapshot):
        if type(c)is not dict or 'kind'not in c:raise ValueError('Invalid scheduled operation')
        if c['kind']=='timer'and set(c)=={'kind','at_ms'}:
            if type(c['at_ms'])is not int:raise ValueError('Integer timer deadline required')
            return NS+'stepTimer model '+snapshot+' '+gate.number(c['at_ms'])
        if c['kind']!='external'or set(c)!={'kind','event','fields','at_ms'}or c['event']not in self.events or type(c['at_ms'])is not int:raise ValueError('Invalid external operation')
        schema=self.m['events'][c['event']]['fields'];fs=c['fields']
        if type(fs)is not dict or set(fs)!=set(schema):raise ValueError('Event field dimensions differ')
        values=self.v.values(fs,schema)
        return NS+'external model '+snapshot+' '+str(self.events.index(c['event']))+' '+values+' '+gate.number(c['at_ms'])
    def expected(self,e,before,step):
        obs='FormalSpecAgent.MachineObserve.'
        if type(e)is not dict:raise ValueError('Invalid microstep expected outcome')
        if set(e)=={'status','fault'}and e['status']=='error':
            if e['fault']not in {'uncovered','conflict','badDelay','invariant','time','timerInjection','pendingTimer','noTimer'}:raise ValueError('Unknown scheduled fault')
            return obs+'Outcome.error .'+e['fault']+' ('+obs+'snapshot schema '+before+')'
        if set(e)!={'status','rule','after','emitted'}or e['status']!='ok'or e['rule']not in [r['id']for r in self.m['transitions']]or type(e['emitted'])is not list:raise ValueError('Invalid microstep success oracle')
        after=self.snapshot(e['after']);messages=[]
        for row in e['emitted']:
            if type(row)is not dict or set(row)!={'message','fields'}or row['message']not in self.messages:raise ValueError('Invalid expected emitted message')
            schema=self.m['messages'][row['message']]['fields']
            if type(row['fields'])is not dict or set(row['fields'])!=set(schema):raise ValueError('Expected emitted fields differ')
            fields=['('+str(i)+', '+packed(row['fields'][n],k)+')'for i,(n,k)in enumerate(schema.items())]
            messages.append('('+str(self.messages.index(row['message']))+', ['+', '.join(fields)+'])')
        ri=next(i for i,r in enumerate(self.m['transitions'])if r['id']==e['rule'])
        # Timer expected events are derived from the rule, not from an assumed
        # scheduler choice. A wrong selected rule/event fails the literal goal.
        ev=self.events.index(self.m['transitions'][ri]['event'])
        return obs+'Outcome.success '+str(ri)+' '+str(ev)+' ('+obs+'snapshot schema '+after+') ['+', '.join(messages)+']'


def packed(value,kind):
    # Only the observation's concrete domain differs: sequence Fin becomes Nat.
    lit=literal(value,kind)
    if kind=='seq32':lit=str(value)
    return '(FormalSpecAgent.MachineObserve.Packed.'+KINDS[kind]+' '+lit+')'


def prepare(task_file,workspace,task_sha256,*,draft=False):
    root=Path(workspace).resolve();task_file=Path(task_file).resolve()
    if not task_file.is_relative_to(root)or gate.sha(task_file)!=task_sha256:raise ValueError('Machine task outside workspace or pin differs')
    t=json.loads(task_file.read_text());keys={'schema','id','model','model_sha256','sources','cases','lean_version','semantics_sha256','adapter_sha256','approved_sha256'}
    if set(t)!=keys or t['schema']!='fsa-lean-machine-task-v1'or t['lean_version']!=gate.VERSION or type(t['id'])is not str or not gate.NAME.fullmatch(t['id']):raise ValueError('Invalid typed machine task schema')
    if type(t['semantics_sha256'])is not dict or set(t['semantics_sha256'])!=set(MODULES)or any(gate.sha(HERE/('lean/'+n+'.lean'))!=t['semantics_sha256'][n]for n in MODULES)or gate.sha(Path(__file__).resolve())!=t['adapter_sha256']:raise ValueError('Machine approval epoch differs')
    mf=gate.inside(root,t['model']);chain=model_files(mf)
    if gate.sha(mf)!=t['model_sha256']or any(not p.is_relative_to(root)for p in chain):raise ValueError('Machine source/model pin differs')
    paths=[task_file,*chain];pinned=set()
    if type(t['sources'])is not list or not t['sources']:raise ValueError('Machine pinned sources required')
    for row in t['sources']:
        if type(row)is not dict or set(row)!={'path','sha256'}:raise ValueError('Invalid machine source row')
        p=gate.inside(root,row['path'])
        if gate.sha(p)!=row['sha256']:raise ValueError('Machine source digest differs')
        paths.append(p);pinned.add(p)
    if not set(chain[1:])<=pinned:raise ValueError('Machine model bases must be pinned')
    view=MachineView(load(mf));s=view.source();cases=t['cases'];goals={
        'get_set_same':'∀ (k : FormalSpecAgent.TypedIR.Kind) (n : Nat) (v : FormalSpecAgent.TypedIR.Value k) (s : FormalSpecAgent.TypedIR.Values), FormalSpecAgent.TypedIR.getValue k ('+NS+'setValue k n v s) n = v',
        'rollback_error':'∀ (s : '+NS+'Snapshot) (f : '+NS+'Fault), '+NS+'rollback s (.error f) = s',
        'cancel_membership':'∀ (s : '+NS+'Snapshot) (n : Nat), ∀ e ∈ ('+NS+'cancelTimer s n).timers, e.timer ≠ n',
        'fire_invariant':'∀ (m : '+NS+'Model) (s : '+NS+'Snapshot) (e : Nat) (f : FormalSpecAgent.TypedIR.Values) (timer : Option Nat) (t : '+NS+'Transition), '+NS+'fire m s e f timer = .ok t → '+NS+'invariantsHold m t.after = true',
    }
    if type(cases)is not list or not 1<=len(cases)<=128:raise ValueError('Scheduled literal cases required')
    ids=set();rows=0
    for i,c in enumerate(cases):
        if type(c)is not dict or set(c)!={'id','initial','steps'}or type(c['id'])is not str or c['id']in ids or type(c['steps'])is not list or not 1<=len(c['steps'])<=128:raise ValueError('Invalid scheduled case')
        ids.add(c['id']);initial=view.snapshot(c['initial']);s+='\ndef initial_'+str(i)+' : '+NS+'Snapshot := '+initial+'\n'
        # Context validity is required, not an assumed postcondition.
        goals['initial_valid_'+str(i)]=NS+'invariantsHold model initial_'+str(i)+' = true'
        previous='initial_'+str(i)
        for j,step in enumerate(c['steps']):
            if type(step)is not dict or 'expected'not in step:raise ValueError('Every operation requires its frozen literal oracle')
            cmd={k:v for k,v in step.items()if k!='expected'};name=str(i)+'_'+str(j)
            expression=view.command(cmd,previous);s+='\ndef result_'+name+' := '+expression+'\n'
            expected=view.expected(step['expected'],previous,cmd)
            goals['witness_'+name]='FormalSpecAgent.MachineObserve.outcome schema '+previous+' result_'+name+' = '+expected
            s+='\ndef after_'+name+' : '+NS+'Snapshot := '+NS+'rollback '+previous+' result_'+name+'\n';previous='after_'+name;rows+=1
    if rows>512:raise ValueError('Scheduled trace resource limit exceeded')
    s+='\n\n'.join('def '+n+' : Prop :=\n  '+p for n,p in goals.items())+'\n\nend Approved\n'
    if not draft and hashlib.sha256(s.encode()).hexdigest()!=t['approved_sha256']:raise ValueError('Frozen machine statements differ')
    inputs={'workspace/'+str(p.relative_to(root)):gate.sha(p)for p in paths}
    for p in [Path(__file__).resolve(),HERE/'lean_typed.py',HERE/'lean_backend.py',HERE/'lean/lean-toolchain',*(HERE/('lean/'+n+'.lean')for n in MODULES)]:inputs['tool/'+str(p.relative_to(HERE))]=gate.sha(p)
    inputs['ir_checker']=gate.sha(HERE.parent/'protocol_lab/ir.py')
    return s,list(goals),inputs
