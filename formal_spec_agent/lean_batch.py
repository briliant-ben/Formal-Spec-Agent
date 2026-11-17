"""Full-batch literal contracts derived from authoritative typed IR."""
import hashlib
import json
from pathlib import Path
from protocol_lab.ir import load,model_files
from . import lean_backend as gate
from .lean_machine import MachineView,packed
from .lean_typed import KINDS,literal

HERE=Path(__file__).resolve().parent
NS='FormalSpecAgent.BatchMachine.'
OBS='FormalSpecAgent.BatchObserve.'
MODULES=['Foundation','ValueOps','TypedIR','TypedMachine','StoreFacts','TimerRank','TimerMinimum','TimerEffects','TimerProgress','BatchMachine','BatchReplay','MachineObserve','BatchObserve']
SCOPE=('Exact typed full-batch literal contracts and generic total timer progress. '
       'Not universal rule preservation before invariant filtering, compiler/native '
       'arithmetic/memory or English specification/protocol correctness.')


class BatchView(MachineView):
    def source(self,*,proof_helpers=False):
        s=super().source().replace('import MachineObserve\n','import BatchObserve\n',1)
        choices=[]
        for i,name in enumerate(self.events):
            fields=self.m['events'][name]['fields'];schema='['+', '.join('(.'+KINDS[k]+', '+str(j)+')'for j,k in enumerate(fields.values()))+']'
            choices.append('if n = '+str(i)+' then '+schema+' else ')
        s+='\ndef eventSchemas (n : Nat) : List (FormalSpecAgent.TypedIR.Kind × Nat) := '+''.join(choices)+'[]\n'
        if proof_helpers:
            rules='['+', '.join('rule_'+str(i)for i in range(len(self.m['transitions'])))+']'
            invariants='['+', '.join(self.expr('invariant_'+str(i))for i in range(len(self.m['invariants'])))+']'
            external='['+', '.join(str(i)for i,n in enumerate(self.events)if self.m['events'][n]['origin']!='timer')+']'
            timers=''.join('if n = '+str(i)+' then '+str(self.events.index(self.m['timers'][t]['event']))+' else 'for i,t in enumerate(self.timers))+'0'
            for name,left,right in [('rules','model.rules',rules),('invariants','model.invariants',invariants),('external_events','model.externalEvents',external)]:
                s+='\ntheorem model_'+name+' : '+left+' = '+right+' := rfl\n'
            s+='\ntheorem model_timer_event (n : Nat) : model.timerEvents n = '+timers+' := rfl\n'
        return s

    def command(self,c,snapshot):
        if type(c)is not dict or 'kind'not in c:raise ValueError('Invalid batch operation')
        if c['kind']=='tick'and set(c)=={'kind','at_ms'}:
            if type(c['at_ms'])is not int:raise ValueError('Integer batch time required')
            return NS+'tick model '+snapshot+' '+gate.number(c['at_ms'])
        if c['kind']!='dispatch'or set(c)!={'kind','event','fields','at_ms'}or c['event']not in self.events or type(c['at_ms'])is not int:raise ValueError('Invalid batch dispatch')
        schema=self.m['events'][c['event']]['fields'];fs=c['fields']
        if type(fs)is not dict or set(fs)!=set(schema):raise ValueError('Batch event dimensions differ')
        return NS+'dispatch model '+snapshot+' '+str(self.events.index(c['event']))+' '+self.v.values(fs,schema)+' '+gate.number(c['at_ms'])

    def full_snapshot(self,s,order):
        # Stronger proof-only representation equality. The ordinary observation
        # remains map-based; neither subject code nor its inputs use this oracle.
        self.snapshot(s)
        if len(order)!=len(set(order))or set(order)!=set(s['timers']):raise ValueError('Proof cache timer representation differs from declared map')
        values=self.v.values(s['variables'],{n:v['type']for n,v in self.m['variables'].items()})
        timers='['+', '.join('⟨'+str(self.timers.index(n))+', '+gate.number(s['timers'][n])+'⟩'for n in order)+']'
        return '({ values := '+values+', state := '+str(self.v.states.index(s['state']))+', now := '+gate.number(s['now_ms'])+', timers := '+timers+' } : FormalSpecAgent.TypedMachine.Snapshot)'

    def full_expected(self,e,order):
        if e['status']=='error':return '.error .'+e['fault'],list(order)
        order=list(order);frames=[]
        for row in e['trace']:
            ri=next(i for i,r in enumerate(self.m['transitions'])if r['id']==row['rule']);rule=self.m['transitions'][ri]
            ev=row['event'];origin=self.m['events'][ev['name']]['origin']
            if origin=='timer':
                timer=next(n for n,t in self.m['timers'].items()if t['event']==ev['name']);order=[n for n in order if n!=timer]
            emitters=[]
            for action in rule['actions']:
                kind,arg=next(iter(action.items()))
                if kind in ('cancel','arm'):
                    timer=arg if kind=='cancel'else arg['timer'];order=[n for n in order if n!=timer]
                    if kind=='arm':order.append(timer)
                elif kind=='emit':emitters.append(arg)
            if len(emitters)!=len(row['emitted']):raise ValueError('Proof cache emit count differs from IR')
            messages=[]
            for action,msg in zip(emitters,row['emitted']):
                if action['message']!=msg['message']:raise ValueError('Proof cache emitted identity differs from IR')
                schema=self.m['messages'][msg['message']]['fields'];fields=[]
                for n in action['fields']:
                    k=schema[n];fields.append('⟨'+str(list(schema).index(n))+', .'+KINDS[k]+', '+literal(msg['fields'][n],k)+'⟩')
                messages.append('({ name := '+str(self.messages.index(msg['message']))+', fields := ['+', '.join(fields)+'] } : FormalSpecAgent.TypedMachine.Message)')
            fields=self.v.values(ev['fields'],self.m['events'][ev['name']]['fields'])
            frames.append('({ after := '+self.full_snapshot(row['after'],order)+', rule := '+str(ri)+', event := '+str(self.events.index(ev['name']))+', fields := '+fields+', emitted := ['+', '.join(messages)+'] } : FormalSpecAgent.TypedMachine.Transition)')
        value='.ok ({ after := '+self.full_snapshot(e['after'],order)+', trace := ['+', '.join(frames)+'] } : FormalSpecAgent.BatchMachine.Batch)'
        return value,order

    def expected(self,e,before,step):
        if type(e)is not dict:raise ValueError('Invalid batch outcome')
        if set(e)=={'status','fault'}and e['status']=='error':
            super().expected(e,before,step)
            return OBS+'Outcome.error .'+e['fault']+' (FormalSpecAgent.MachineObserve.snapshot schema '+before+')'
        if set(e)!={'status','after','trace'}or e['status']!='ok'or type(e['trace'])is not list or len(e['trace'])>512:raise ValueError('Invalid batch success/trace')
        after=self.snapshot(e['after']);trace=[]
        for t in e['trace']:
            if type(t)is not dict or set(t)!={'rule','event','at_ms','after','emitted'}or type(t['at_ms'])is not int or type(t['event'])is not dict or set(t['event'])!={'name','fields'}:raise ValueError('Invalid batch transition oracle')
            ev=t['event'];name=ev['name']
            if name not in self.events or type(ev['fields'])is not dict or set(ev['fields'])!=set(self.m['events'][name]['fields']):raise ValueError('Invalid trace event fields')
            self.v.values(ev['fields'],self.m['events'][name]['fields'])
            ri=next((i for i,r in enumerate(self.m['transitions'])if r['id']==t['rule']),None)
            if ri is None or self.m['transitions'][ri]['event']!=name or t['after']['now_ms']!=t['at_ms']:raise ValueError('Trace rule/event/time identity differs')
            super().expected(dict(status='ok',rule=t['rule'],after=t['after'],emitted=t['emitted']),before,{})
            fields='['+', '.join(packed(ev['fields'][n],k)for n,k in self.m['events'][name]['fields'].items())+']';messages=[]
            for msg in t['emitted']:
                schema=self.m['messages'][msg['message']]['fields'];fs='['+', '.join('('+str(i)+', '+packed(msg['fields'][n],k)+')'for i,(n,k)in enumerate(schema.items()))+']'
                messages.append('('+str(self.messages.index(msg['message']))+', '+fs+')')
            trace.append('({ rule := '+str(ri)+', event := '+str(self.events.index(name))+', fields := '+fields+', after := FormalSpecAgent.MachineObserve.snapshot schema '+self.snapshot(t['after'])+', emitted := ['+', '.join(messages)+'] } : '+OBS+'SeenTransition)')
        return OBS+'Outcome.success (FormalSpecAgent.MachineObserve.snapshot schema '+after+') ['+', '.join(trace)+']'


def prepare(task_file,workspace,task_sha256,*,draft=False):
    root=Path(workspace).resolve();task_file=Path(task_file).resolve()
    if not task_file.is_relative_to(root)or gate.sha(task_file)!=task_sha256:raise ValueError('Batch task outside workspace or pin differs')
    t=json.loads(task_file.read_text());keys={'schema','id','model','model_sha256','sources','cases','lean_version','semantics_sha256','adapter_sha256','approved_sha256'}
    if set(t)!=keys or t['schema']!='fsa-lean-batch-task-v1'or t['lean_version']!=gate.VERSION or type(t['id'])is not str or not gate.NAME.fullmatch(t['id']):raise ValueError('Invalid batch task schema')
    if type(t['semantics_sha256'])is not dict or set(t['semantics_sha256'])!=set(MODULES)or any(gate.sha(HERE/('lean/'+n+'.lean'))!=t['semantics_sha256'][n]for n in MODULES)or gate.sha(Path(__file__).resolve())!=t['adapter_sha256']:raise ValueError('Batch approval epoch differs')
    mf=gate.inside(root,t['model']);chain=model_files(mf)
    if gate.sha(mf)!=t['model_sha256']or any(not p.is_relative_to(root)for p in chain):raise ValueError('Batch model pin/path differs')
    paths=[task_file,*chain];pinned=set()
    if type(t['sources'])is not list or not t['sources']:raise ValueError('Batch pinned sources required')
    for row in t['sources']:
        if type(row)is not dict or set(row)!={'path','sha256'}:raise ValueError('Invalid batch source pin')
        p=gate.inside(root,row['path'])
        if gate.sha(p)!=row['sha256']:raise ValueError('Batch source digest differs')
        paths.append(p);pinned.add(p)
    if not set(chain[1:])<=pinned:raise ValueError('Batch bases must be pinned')
    view=BatchView(load(mf));s=view.source(proof_helpers=True);cases=t['cases']
    goals={'timer_progress':'∀ (m : FormalSpecAgent.TypedMachine.Model) (s : FormalSpecAgent.TypedMachine.Snapshot) (limit : Int) (entry : FormalSpecAgent.TypedMachine.TimerEntry) (t : FormalSpecAgent.TypedMachine.Transition), FormalSpecAgent.TimerRank.WellTimed s → s.now ≤ limit → FormalSpecAgent.TypedMachine.nextTimer s = some entry → entry.due ≤ limit → FormalSpecAgent.TypedMachine.stepTimer m s entry.due = .ok t → FormalSpecAgent.TimerRank.WellTimed t.after ∧ t.after.now = entry.due ∧ Prod.Lex Nat.lt Nat.lt (FormalSpecAgent.TimerRank.rank limit t.after) (FormalSpecAgent.TimerRank.rank limit s)',
           'rollback_error':'∀ (s : FormalSpecAgent.TypedMachine.Snapshot) (f : FormalSpecAgent.TypedMachine.Fault), '+NS+'rollback s (.error f) = s'}
    if type(cases)is not list or not 1<=len(cases)<=128:raise ValueError('Frozen batch cases required')
    ids=set();rows=0
    for i,c in enumerate(cases):
        if type(c)is not dict or set(c)!={'id','initial','steps'}or type(c['id'])is not str or c['id']in ids or type(c['steps'])is not list or not 1<=len(c['steps'])<=128:raise ValueError('Invalid batch case')
        ids.add(c['id']);s+='\ndef initial_'+str(i)+' : FormalSpecAgent.TypedMachine.Snapshot := '+view.snapshot(c['initial'])+'\n'
        goals['initial_valid_'+str(i)]='FormalSpecAgent.TypedMachine.invariantsHold model initial_'+str(i)+' = true ∧ FormalSpecAgent.TimerRank.WellTimed initial_'+str(i)
        before='initial_'+str(i);order=sorted(c['initial']['timers'])
        for j,step in enumerate(c['steps']):
            if type(step)is not dict or 'expected'not in step:raise ValueError('Batch operation oracle required')
            name=str(i)+'_'+str(j);cmd={k:v for k,v in step.items()if k!='expected'};s+='\ndef result_'+name+' := '+view.command(cmd,before)+'\n'
            full,order=view.full_expected(step['expected'],order)
            goals['execution_'+name]='result_'+name+' = '+full
            goals['witness_'+name]=OBS+'outcome schema eventSchemas '+before+' result_'+name+' = '+view.expected(step['expected'],before,cmd)
            s+='\ndef after_'+name+' : FormalSpecAgent.TypedMachine.Snapshot := '+NS+'rollback '+before+' result_'+name+'\n';before='after_'+name;rows+=1
    if rows>512:raise ValueError('Batch trace resource limit exceeded')
    s+='\n\n'.join('def '+n+' : Prop :=\n  '+p for n,p in goals.items())+'\n\nend Approved\n'
    if not draft and hashlib.sha256(s.encode()).hexdigest()!=t['approved_sha256']:raise ValueError('Frozen batch statements differ')
    inputs={'workspace/'+str(p.relative_to(root)):gate.sha(p)for p in paths}
    for p in [Path(__file__).resolve(),HERE/'lean_machine.py',HERE/'lean_typed.py',HERE/'lean_backend.py',HERE/'lean/lean-toolchain',*(HERE/('lean/'+n+'.lean')for n in MODULES)]:inputs['tool/'+str(p.relative_to(HERE))]=gate.sha(p)
    inputs['ir_checker']=gate.sha(HERE.parent/'protocol_lab/ir.py')
    return s,list(goals),inputs
