"""Typed, shared pure IR expression views; no evaluator callbacks or solver."""
import hashlib
import json
import argparse
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

from protocol_lab.ir import load, model_files, value_ok
from . import lean_backend as gate

HERE = Path(__file__).resolve().parent
NS = 'FormalSpecAgent.TypedIR.'
KINDS = {'int':'integer', 'bool':'boolean', 'string':'text', 'bytes':'octets', 'seq32':'sequence'}
OPS = {
    'add':('add',('int','int'),'int'), 'mul':('mul',('int','int'),'int'),
    'sub':('sub',('int','int'),'int'), 'min':('minimum',('int','int'),'int'),
    'le':('intLe',('int','int'),'bool'), 'ge':('intGe',('int','int'),'bool'),
    'and':('boolAnd',('bool','bool'),'bool'), 'or':('boolOr',('bool','bool'),'bool'),
    'not':('boolNot',('bool',),'bool'), 'implies':('implies',('bool','bool'),'bool'),
    'seq_add':('seqAdd',('seq32','int'),'seq32'),
    'seq_distance':('seqDistance',('seq32','seq32'),'int'),
    'seq_comparable':('seqComparable',('seq32','seq32'),'bool'),
    'seq_lt':('seqLt',('seq32','seq32'),'bool'), 'seq_le':('seqLe',('seq32','seq32'),'bool'),
    'bytes_len':('bytesLength',('bytes',),'int'),
    'bytes_concat':('concat',('bytes','bytes'),'bytes'),
    'bytes_slice':('slice',('bytes','int','int'),'bytes'),
    'bytes_at_or_zero':('byteAt',('bytes','int'),'int'),
    'bytes_pack8_mod':('pack8',('int',),'bytes'),
    'bytes_pack16be_mod':('pack16',('int',),'bytes'),
    'bytes_pack32be_mod':('pack32',('int',),'bytes'),
    'bytes_internet_checksum16':('checksum',('bytes',),'int'),
}
SUPPORTED_OPS = set(OPS) | {'eq','ne','ite'}
SCOPE = ('Typed pure expression views and frozen literal values for the admitted '
         'IR0.5/0.6 atomic fragment. Not EFSM safety, scheduling, reachability, '
         'native memory/overflow/compiler or specification interpretation correctness.')


def literal(value, kind):
    if kind not in KINDS or not value_ok(value, kind): raise ValueError('Invalid typed IR value')
    if kind == 'int': return gate.number(value)
    if kind == 'bool': return str(value).lower()
    if kind == 'seq32': return '(⟨'+str(value)+', by decide⟩ : FormalSpecAgent.ValueOps.Seq32)'
    if kind == 'string':
        if any(0xD800 <= ord(c) <= 0xDFFF for c in value): raise ValueError('Unicode surrogate outside Lean scalar-string domain')
        return '(String.ofList ['+', '.join('Char.ofNat '+str(ord(c)) for c in value)+'])'
    # Exact run factoring keeps large constant buffers compact without replacing
    # octets by a length projection or changing order/content.
    def plain(xs):return '['+', '.join('⟨'+str(b)+', by decide⟩'for b in xs)+']'
    parts=[];pending=[];i=0
    while i<len(value):
        j=i+1
        while j<len(value)and value[j]==value[i]:j+=1
        if j-i>=4:
            if pending:parts.append(plain(pending));pending=[]
            parts.append('List.replicate '+str(j-i)+' (⟨'+str(value[i])+', by decide⟩ : FormalSpecAgent.Byte)')
        else:pending.extend(value[i:j])
        i=j
    if pending:parts.append(plain(pending))
    return '('+' ++ '.join(parts or['[]'])+' : FormalSpecAgent.Bytes)'


class View:
    def __init__(self, model):
        self.model = model
        if model['ir_version'] not in ('0.5','0.6') or model['semantics'] != 'flat-efsm-atomic-ordered-v1': raise ValueError('Typed view requires IR0.5/0.6 atomic-v1')
        if any(v['type'] not in KINDS for v in model['variables'].values()) or any(k not in KINDS for e in model['events'].values() for k in e['fields'].values()): raise ValueError('Unsupported typed IR value kind')
        self.variables = list(model['variables']); self.states = model['states']; self.timers = list(model['timers'])
        self.nodes = []; self.memo = {}; self.roots = {}; self.operators = set(); self.node_ops = []; self.actions = {}

    def node(self, kind, constructor, parameters, key, ops=()):
        if key in self.memo: return self.memo[key]
        if len(self.nodes) >= 100000: raise ValueError('Typed expression node resource limit exceeded')
        n = len(self.nodes); name = 'e'+str(n)
        self.nodes.append(('def '+name+' : '+NS+'Expr .'+KINDS[kind]+' :=\n  '+NS+'Expr.'+constructor+' '+parameters+'\n', kind))
        self.memo[key] = n; self.node_ops.append(set(ops)); return n

    def expr(self, e, event=None, depth=0):
        if depth > 128: raise ValueError('Typed expression depth resource limit exceeded')
        if type(e) in (bool,int,str):
            kind = {bool:'bool',int:'int',str:'string'}[type(e)]
            return self.node(kind,'literal','.'+KINDS[kind]+' '+literal(e,kind),('literal',kind,e))
        if type(e) is not dict: raise ValueError('Unsupported typed expression literal')
        if set(e) in ({'bytes'},{'seq'}):
            kind = 'bytes' if 'bytes' in e else 'seq32'; v = e[next(iter(e))]
            key = tuple(v) if kind == 'bytes' and type(v) is list else v
            return self.node(kind,'literal','.'+KINDS[kind]+' '+literal(v,kind),('literal',kind,key))
        if set(e) in ({'var'},{'event'}):
            variable = 'var' in e; name = e['var' if variable else 'event']
            schema = {n:v['type'] for n,v in self.model['variables'].items()} if variable else self.model['events'].get(event,{}).get('fields',{})
            if name not in schema: raise ValueError('Unknown typed variable/event field')
            kind = schema[name]; index = list(schema).index(name); tag = 'variable' if variable else 'field'
            return self.node(kind,tag,'.'+KINDS[kind]+' '+str(index),(tag,kind,index))
        if set(e) in ({'state'},{'timer_active'}):
            state = 'state' in e; name = e['state' if state else 'timer_active']; names = self.states if state else self.timers
            if name not in names: raise ValueError('Unknown typed state/timer')
            tag = 'stateIs' if state else 'timerActive'; index = names.index(name)
            return self.node('bool',tag,str(index),(tag,index))
        if set(e) != {'op','args'} or type(e['args']) is not list: raise ValueError('Unsupported typed expression shape')
        op = e['op']
        if type(op)is not str or op not in SUPPORTED_OPS: raise ValueError('Unsupported typed IR operator: '+str(op))
        if op=='bytes_pack32be_mod'and self.model['ir_version']!='0.6':raise ValueError('Word32 packing requires IR0.6')
        children = [self.expr(a,event,depth+1) for a in e['args']]; kinds = tuple(self.nodes[n][1] for n in children)
        prefix = ''
        if op in ('eq','ne'):
            if len(kinds)!=2 or kinds[0]!=kinds[1]: raise ValueError('Typed equality kind mismatch')
            ctor, kind = ('equal' if op=='eq' else 'notEqual'), 'bool'; prefix = '.'+KINDS[kinds[0]]+' '
        elif op == 'ite':
            if len(kinds)!=3 or kinds[0]!='bool' or kinds[1]!=kinds[2]: raise ValueError('Typed conditional kind mismatch')
            ctor,kind = 'choose',kinds[1]; prefix = '.'+KINDS[kind]+' '
        else:
            ctor, signature, kind = OPS[op]
            if kinds != signature: raise ValueError('Typed operator signature mismatch: '+op)
        self.operators.add(op); ops = {op}.union(*(self.node_ops[n] for n in children))
        return self.node(kind,ctor,prefix+' '.join('e'+str(n) for n in children),(op,kind,tuple(children)),ops)

    def root(self, name, expression, expected, event=None, origin=None):
        n = self.expr(expression,event)
        if self.nodes[n][1] != expected: raise ValueError('Typed root result kind differs: '+name)
        self.roots[name] = dict(node=n,kind=expected,event=event,origin=origin)

    def build(self):
        for i,(variable,v) in enumerate(self.model['variables'].items()):
            kind=v['type'];value=v['initial'];key=tuple(value)if kind=='bytes'else value
            n=self.node(kind,'literal','.'+KINDS[kind]+' '+literal(value,kind),('literal',kind,key))
            self.roots['initial_'+str(i)]=dict(node=n,kind=kind,event=None,origin=dict(variable=variable,role='initial'))
        for i,r in enumerate(self.model['transitions']):
            event=r['event'];origin=dict(rule=r['id'],requirements=r['requirements']); self.root('guard_'+str(i),r['guard'],'bool',event,dict(**origin,role='guard'))
            for j,a in enumerate(r['actions']):
                tag,x=next(iter(a.items()));self.actions[tag]=self.actions.get(tag,0)+1;name='action_'+str(i)+'_'+str(j)
                provenance=dict(**origin,role=tag,action=j)
                def add(label,expr,kind):self.root(label,expr,kind,event,provenance)
                if tag=='set': add(name,x['value'],self.model['variables'][x['var']]['type'])
                elif tag in ('emit','emit_if'):
                    if tag=='emit_if':add(name+'_when',x['when'],'bool')
                    for k,e in x['fields'].items():
                        self.root(name+'_'+str(list(x['fields']).index(k)),e,self.model['messages'][x['message']]['fields'][k],event,dict(**provenance,message=x['message'],field=k))
                elif tag in ('arm','arm_if'):
                    if tag=='arm_if':add(name+'_when',x['when'],'bool')
                    add(name,x['delay_ms'],'int')
                elif tag=='cancel_if':add(name+'_when',x['when'],'bool')
                elif tag!='cancel':raise ValueError('Unsupported typed-view action: '+tag)
            if r.get('target_cases'):raise ValueError('Post-target semantics outside typed view')
        for i,inv in enumerate(self.model['invariants']):self.root('invariant_'+str(i),inv['assert'],'bool',origin=dict(invariant=inv['id'],requirements=inv['requirements']))
        return self

    def source(self):
        return 'import TypedIR\n\nset_option maxRecDepth 16384\n\nnamespace Approved\n\n'+ '\n'.join(s for s,k in self.nodes)

    def values(self, values, schema):
        columns = [('integers','int',0),('booleans','bool',False),('texts','string',''),('buffers','bytes',[]),('sequences','seq32',0)]
        result=[]
        for column,kind,default in columns:
            body=''.join('if n = '+str(i)+' then '+literal(values[name],kind)+' else ' for i,(name,k) in enumerate(schema.items()) if k==kind)
            result.append(column+' := fun n => '+body+literal(default,kind))
        return '({ '+', '.join(result)+' } : '+NS+'Values)'

    def context(self, context, event):
        if type(context)is not dict or set(context)!={'variables','fields','state','active_timers'}:raise ValueError('Explicit typed context required')
        overrides=context['variables'];fields=context['fields'];active=context['active_timers']
        schema={n:v['type'] for n,v in self.model['variables'].items()};field_schema=self.model['events'][event]['fields'] if event is not None else {}
        if type(overrides)is not dict or not set(overrides)<=set(schema) or type(fields)is not dict or set(fields)!=set(field_schema):raise ValueError('Typed context field/variable schema mismatch')
        values={n:v['initial'] for n,v in self.model['variables'].items()};values.update(overrides)
        if context['state']not in self.states or type(active)is not list or any(n not in self.timers for n in active)or len(set(active))!=len(active):raise ValueError('Typed state/active-timer mismatch')
        store=self.values(values,schema);env=self.values(fields,field_schema)
        return '({ store := '+store+', fields := '+env+', state := '+str(self.states.index(context['state']))+', activeTimers := ['+', '.join(str(self.timers.index(n))for n in active)+'] } : '+NS+'Context)'


def prepare(task_file,workspace,task_sha256,*,draft=False):
    root=Path(workspace).resolve();task_file=Path(task_file).resolve()
    if not task_file.is_relative_to(root)or gate.sha(task_file)!=task_sha256:raise ValueError('Typed task outside workspace or digest mismatch')
    t=json.loads(task_file.read_text());keys={'schema','id','model','model_sha256','sources','cases','lean_version','semantics_sha256','adapter_sha256','approved_sha256'}
    if set(t)!=keys or t['schema']!='fsa-lean-typed-expression-task-v1'or t['lean_version']!=gate.VERSION:raise ValueError('Unsupported typed task schema/version')
    if type(t['id'])is not str or not gate.NAME.fullmatch(t['id']):raise ValueError('Invalid typed task identity')
    modules=['Foundation','ValueOps','TypedIR']
    if type(t['semantics_sha256'])is not dict or set(t['semantics_sha256'])!=set(modules)or any(gate.sha(HERE/('lean/'+n+'.lean'))!=t['semantics_sha256'][n]for n in modules)or gate.sha(Path(__file__).resolve())!=t['adapter_sha256']:raise ValueError('Typed semantic/adapter approval epoch changed')
    mf=gate.inside(root,t['model']);chain=model_files(mf)
    if gate.sha(mf)!=t['model_sha256']or any(not p.is_relative_to(root)for p in chain):raise ValueError('Typed model digest/path mismatch')
    paths=[task_file,*chain];pinned=set()
    if type(t['sources'])is not list or not t['sources']:raise ValueError('Typed sources required')
    for row in t['sources']:
        if type(row)is not dict or set(row)!={'path','sha256'}:raise ValueError('Invalid typed source binding')
        p=gate.inside(root,row['path'])
        if gate.sha(p)!=row['sha256']:raise ValueError('Typed source digest mismatch')
        paths.append(p);pinned.add(p)
    if not set(chain[1:])<=pinned:raise ValueError('Typed model bases must be pinned')
    m=load(mf);view=View(m).build();source=view.source();cases=t['cases'];covered=set()
    ops='FormalSpecAgent.ValueOps.'
    goals={
        'checksum_range':'∀ (data : FormalSpecAgent.Bytes), 0 ≤ '+ops+'checksum data ∧ '+ops+'checksum data ≤ 65535',
        'sequence_distance_range':'∀ (a b : '+ops+'Seq32), 0 ≤ '+ops+'seqDistance a b ∧ '+ops+'seqDistance a b < 4294967296',
        'half_space_unordered':'∀ (a b : '+ops+'Seq32), '+ops+'seqDistance a b = 2147483648 → '+ops+'seqComparable a b = false ∧ '+ops+'seqLt a b = false ∧ '+ops+'seqLe a b = false',
    }
    if type(cases)is not list or not 1<=len(cases)<=256:raise ValueError('Typed literal cases required')
    contexts={}
    for i,c in enumerate(cases):
        if type(c)is not dict or set(c)!={'target','context','expected'}or type(c['target'])is not str or c['target']not in view.roots:raise ValueError('Unknown typed literal target')
        target=view.roots[c['target']];n=target['node'];covered|=view.node_ops[n]
        ctx=view.context(c['context'],target['event']);expected=literal(c['expected'],target['kind'])
        if ctx in contexts:body='context_'+str(contexts[ctx])
        else:contexts[ctx]=i;body=ctx
        source+='\ndef context_'+str(i)+' : '+NS+'Context :=\n  '+body+'\n'
        goals['witness_'+str(i)]=NS+'eval e'+str(n)+' context_'+str(i)+' = '+expected
    if covered!=view.operators:raise ValueError('Every model operator needs a frozen typed literal witness')
    source+='\n'+'\n\n'.join('def '+name+' : Prop :=\n  '+s for name,s in goals.items())+'\n\nend Approved\n'
    if not draft and hashlib.sha256(source.encode()).hexdigest()!=t['approved_sha256']:raise ValueError('Typed statements differ from frozen approval')
    inputs={'workspace/'+str(p.relative_to(root)):gate.sha(p)for p in paths}
    for p in [Path(__file__).resolve(),HERE/'lean_backend.py',*(HERE/('lean/'+n+'.lean')for n in modules),HERE/'lean/lean-toolchain']:
        inputs['tool/'+str(p.relative_to(HERE))]=gate.sha(p)
    inputs['ir_checker']=gate.sha(HERE.parent/'protocol_lab/ir.py')
    return source,list(goals),inputs


def model_view(model_file,workspace,model_sha256):
    root=Path(workspace).resolve();model_file=Path(model_file).resolve();chain=model_files(model_file)
    if not model_file.is_relative_to(root)or gate.sha(model_file)!=model_sha256 or any(not p.is_relative_to(root)for p in chain):raise ValueError('Typed model pin/path mismatch')
    view=View(load(model_file)).build()
    source=view.source()+'\nend Approved\n'
    inputs={'workspace/'+str(p.relative_to(root)):gate.sha(p)for p in chain}
    for p in [Path(__file__).resolve(),HERE/'lean_backend.py',HERE/'lean/lean-toolchain',*(HERE/('lean/'+n+'.lean')for n in ['Foundation','ValueOps','TypedIR'])]:
        inputs['tool/'+str(p.relative_to(HERE))]=gate.sha(p)
    inputs['ir_checker']=gate.sha(HERE.parent/'protocol_lab/ir.py')
    summary=dict(nodes=len(view.nodes),roots=len(view.roots),root_bindings=view.roots,operators=sorted(view.operators),actions=view.actions,states=len(view.states),timers=len(view.timers),rules=len(view.model['transitions']),invariants=len(view.model['invariants']))
    return source,inputs,summary


def check_types(model_file,workspace,out,model_sha256,lean='lean'):
    out=Path(out).resolve();root=Path(workspace).resolve()
    if out.exists()or out.is_relative_to(root)or out.is_relative_to(HERE.parent):raise ValueError('Fresh external typecheck output required')
    source,inputs,summary=model_view(model_file,root,model_sha256)
    out.mkdir(parents=True);modules=['Foundation','ValueOps','TypedIR','ModelView']
    for n in modules[:-1]:(out/(n+'.lean')).write_bytes((HERE/('lean/'+n+'.lean')).read_bytes())
    (out/'ModelView.lean').write_text(source)
    sources={p.name:gate.sha(p)for p in out.glob('*.lean')}
    for n in sources:(out/n).chmod(0o444)
    result=dict(schema='fsa-lean-typecheck-result-v1',status='incomplete',scope='Derived full-model pure-expression typing only. No EFSM safety, literal value contract, scheduling, native compiler or protocol proof.',model_sha256=model_sha256,inputs=inputs,sources=sources,view=summary,commands=[],efsm_safety_proved=False,protocol_correctness_proved=False,compiler_correctness_proved=False)
    def save():
        result['outputs']={p.name:gate.sha(p)for p in out.iterdir()if p.is_file()and p.name!='result.json'}
        gate.write(out/'result.json',result);return result
    tool=shutil.which(str(lean))
    if not tool:result.update(status='blocked',classification='environment');return save()
    tool=str(Path(tool).resolve());version=subprocess.check_output([tool,'--version'],text=True,timeout=15)
    if not re.search(r'\bversion '+re.escape(gate.VERSION)+r'(?:,|\))',version):raise ValueError('Pinned Lean version required')
    result.update(lean_version=version.strip(),lean_binary_sha256=gate.sha(tool));env=dict(PATH=os.defpath,LEAN_PATH=str(out),LANG='C.UTF-8')
    for n in modules:
        try:
            p=subprocess.run([tool,'-o',n+'.olean',n+'.lean'],cwd=out,env=env,capture_output=True,text=True,timeout=120)
            stdout,stderr,rc=p.stdout,p.stderr,p.returncode
        except subprocess.TimeoutExpired as e:
            stdout=(e.stdout or b'').decode()if isinstance(e.stdout,bytes)else(e.stdout or'');stderr='Pinned typecheck wall-clock timeout';rc=None
        (out/(n+'.stdout')).write_text(stdout);(out/(n+'.stderr')).write_text(stderr)
        result['commands'].append(dict(module=n,returncode=rc,stdout_sha256=gate.sha(out/(n+'.stdout')),stderr_sha256=gate.sha(out/(n+'.stderr'))))
        if rc!=0:result.update(status='fail',classification='resource_unknown'if gate.resource_failure(rc,stdout,stderr)else'typecheck_failure',failed_module=n);break
    else:result['status']='typed_ir_view_checked'
    if model_view(model_file,root,model_sha256)[1]!=inputs or any(gate.sha(out/n)!=h for n,h in sources.items()):result.update(status='invalidated_inputs',classification='evidence_changed')
    return save()


def type_main(argv=None):
    p=argparse.ArgumentParser(description='Typecheck a complete derived IR expression view; not a safety/protocol proof')
    p.add_argument('model',type=Path);p.add_argument('--workspace',type=Path,required=True);p.add_argument('--model-sha256',required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--lean',default='lean')
    a=p.parse_args(argv)
    try:
        r=check_types(a.model,a.workspace,a.out,a.model_sha256,a.lean);print(json.dumps(r));return 0 if r['status']=='typed_ir_view_checked'else 1
    except (ValueError,TypeError,KeyError,OSError,subprocess.SubprocessError)as e:
        print(json.dumps(dict(status='rejected',reason=str(e))),file=sys.stderr);return 2
