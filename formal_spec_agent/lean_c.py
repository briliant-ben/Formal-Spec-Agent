"""Strict per-output C-expression reification; no C source is executed here."""
import hashlib
import json
from pathlib import Path
import re

from protocol_lab.ir import load,model_files,infer,value_ok
from . import lean_backend as gate

HERE=Path(__file__).resolve().parent
RUNTIME=HERE.parent/'protocol_lab/codegen/runtime.c'
HARNESS=HERE.parent/'protocol_lab/codegen/harness.c'
SCOPE='Selected parsed C expression equals the IR lowering and refines its pure value semantics under pinned runtime/ABI contracts. Not C memory/compiler, EFSM scheduling, failure/rollback or whole-protocol correctness.'
DECIMAL=re.compile(r'(?:0|[1-9][0-9]*)\Z')
TOKEN=re.compile(r'\s+|//[^\n]*|/\*[\s\S]*?\*/|"(?:\\[\s\S]|[^"\\\r\n])*"|\'(?:\\[\s\S]|[^\'\\\r\n])*\'|[A-Za-z_][A-Za-z0-9_]*|[0-9]+|->|[^\s]')


def tokens(source):
    result=[]
    for match in TOKEN.finditer(source):
        x=match.group()
        if x in ('"', "'") or (x=='/'and source[match.end():].startswith('*')):
            raise ValueError('Unterminated C string/character/comment')
        if not x.isspace()and not x.startswith(('//','/*')):result.append(x)
    return result


def body_at(ts,opening):
    depth=0
    for j in range(opening,len(ts)):
        if ts[j]=='{':depth+=1
        elif ts[j]=='}':
            depth-=1
            if not depth:return ts[opening+1:j],j+1
    raise ValueError('Unclosed C function')


def definitions(ts,name,ret,params,inline=False):
    header=['static']+(['inline']if inline else[])+[ret,name,'(']+tokens(params)+[')','{']
    found=[]
    for i in range(len(ts)-len(header)+1):
        if ts[i:i+len(header)]==header:found.append(body_at(ts,i+len(header)-1)[0])
    if len(found)!=1:raise ValueError('Missing or ambiguous C definition: '+name)
    return found[0]


def node(name,*args):return (name,*args)


def parse_expression(source,fields,rule_index,variable_index):
    # Reject preprocessing not modeled by this deliberately small C grammar.
    if not source.isascii():raise ValueError('Non-ASCII C source outside supported profile')
    if len(source.encode())>8*1024*1024:raise ValueError('C source size limit exceeded')
    first=re.match(r'#define STRING_COUNT [0-9]+\n',source)
    runtime=RUNTIME.read_text()
    if not first or not source[first.end():].startswith(runtime):raise ValueError('C runtime differs from pinned helper contracts')
    suffix=HARNESS.read_text()+'\n'
    if not source.endswith(suffix):raise ValueError('C harness differs from the pinned profile')
    rest=source[first.end()+len(runtime):-len(suffix)]
    if '\\\n' in rest or '\\\r\n' in rest or '??' in rest:raise ValueError('Unsupported C preprocessing/line splicing')
    ts=tokens(rest)
    if '#'in ts:raise ValueError('Unsupported extra C preprocessing directive')
    body=definitions(ts,'rule_action_'+str(rule_index),'int','Machine *m,int64_t *f,Bytes *bf,Buffer *log')
    prefix=tokens('Buffer messages={{0},0}; int emitted=0; (void)f; (void)bf; (void)emitted; m->v['+str(variable_index)+']=')
    if body[:len(prefix)]!=prefix:raise ValueError('Selected assignment must be first with the exact native action prefix')
    try:end=body.index(';',len(prefix))
    except ValueError:raise ValueError('Missing selected C assignment terminator')
    used_helpers={};active=[];fuel=[20000]
    class Parser:
        def __init__(self,t):self.ts=t;self.i=0
        def take(self,t=None):
            if self.i>=len(self.ts):raise ValueError('Incomplete C expression')
            v=self.ts[self.i];self.i+=1
            if t is not None and v!=t:raise ValueError('Unexpected C token: '+v)
            return v
        def peek(self):return self.ts[self.i]if self.i<len(self.ts)else None
        def expr(self,kind,depth=0):
            fuel[0]-=1
            if fuel[0]<0:raise ValueError('C expression expansion limit exceeded')
            if depth>64:raise ValueError('C expression/helper depth exceeded')
            t=self.take()
            if t=='(':
                # Parenthesized group or C conditional. Determine the top-level
                # question mark before choosing the condition's boolean type.
                start=self.i;balance=0;conditional=False
                for x in self.ts[start:]:
                    if x=='(':balance+=1
                    elif x==')':
                        if balance==0:break
                        balance-=1
                    elif x=='?'and balance==0:conditional=True;break
                if conditional:
                    c=self.expr('bool',depth+1);self.take('?');yes=self.expr(kind,depth+1);self.take(':');no=self.expr(kind,depth+1);self.take(')')
                    return node('choose',c,yes,no)
                if self.peek()=='-':
                    self.take('-');v=self.expr('int',depth+1);self.take(')')
                    if kind!='int'or v[0]!='integer':raise ValueError('Only signed integer literals may be negated')
                    if not -(2**63)<=-v[1]<2**63:raise ValueError('Negated C literal outside signed64')
                    return node('integer',-v[1])
                e=self.expr(kind,depth+1);self.take(')');return e
            if t in ('f','bf'):
                self.take('[');slot=self.take();self.take(']')
                if not DECIMAL.fullmatch(slot)or int(slot)>=len(fields):raise ValueError('Unknown C event slot')
                n=int(slot);actual=list(fields.values())[n]
                if actual!=kind or (t=='bf')!=(kind=='bytes'):raise ValueError('C event slot/type mismatch')
                return node({'int':'intField','bool':'boolField','bytes':'bytesField'}[kind],n)
            if t=='byte_at_or_zero':
                if kind!='int':raise ValueError('C read result type mismatch')
                self.take('(');b=self.expr('bytes',depth+1);self.take(',');i=self.expr('int',depth+1);self.take(')');return node('read',b,i)
            if re.fullmatch(r'shared_expr_[0-9]+',t):
                self.take('(');self.take('m');self.take(',');f=self.take();self.take(',');bf=self.take();self.take(')')
                if (f,bf)not in [('f','bf'),('NULL','NULL')]:raise ValueError('Changed shared helper arguments')
                if t in active:raise ValueError('C helper cycle')
                helper=definitions(ts,t,'Bytes'if kind=='bytes'else'int64_t','Machine *m,int64_t *f,Bytes *bf',inline=True)
                pre=tokens('(void)m; (void)f; (void)bf; return')
                if helper[:len(pre)]!=pre or helper[-1]!=';'or ';'in helper[len(pre):-1]:raise ValueError('C helper is not one pure return expression')
                active.append(t);p=Parser(helper[len(pre):-1]);e=p.expr(kind,depth+1);p.finish();active.pop()
                if f=='NULL'and any(k in repr(e)for k in ['intField','boolField','bytesField']):raise ValueError('NULL helper arguments with event-dependent body')
                used_helpers[t]=' '.join(helper);return e
            if t=='INT64_C':
                self.take('(');n=self.take();self.take(')')
                if not DECIMAL.fullmatch(n)or int(n)>2**63-1:raise ValueError('C integer literal outside signed64')
                value=int(n)
            elif t=='INT64_MIN':value=-(2**63)
            elif DECIMAL.fullmatch(t)and int(t)<=2**63-1:value=int(t)
            else:raise ValueError('Unsupported C expression token: '+t)
            if kind=='bool'and value in (0,1):return node('boolean',bool(value))
            if kind=='int':return node('integer',value)
            raise ValueError('C literal type mismatch')
        def finish(self):
            if self.i!=len(self.ts):raise ValueError('Unconsumed C expression tokens')
    p=Parser(body[len(prefix):end]);expression=p.expr('int');p.finish()
    return expression,dict(expression_tokens=' '.join(body[len(prefix):end]),expanded_helpers=used_helpers)


def ir_tree(e,m,event):
    if type(e)is bool:return node('boolean',e)
    if type(e)is int:
        if not -(2**63)<=e<2**63:raise ValueError('IR literal outside signed64')
        return node('integer',e)
    if type(e)is not dict:raise ValueError('Unsupported IR expression literal')
    if set(e)=={'event'}:
        fields=m['events'][event]['fields'];n=list(fields).index(e['event']);k=fields[e['event']]
        if k not in ('int','bool','bytes'):raise ValueError('Unsupported IR field type')
        return node({'int':'intField','bool':'boolField','bytes':'bytesField'}[k],n)
    if set(e)=={'op','args'}and e['op']in ('ite','bytes_at_or_zero'):
        return node({'ite':'choose','bytes_at_or_zero':'read'}[e['op']],*(ir_tree(a,m,event)for a in e['args']))
    raise ValueError('Unsupported IR operator/state read in C correspondence fragment')


def lean_tree(e,c=False):
    tag,*args=e
    names={'intField':'intSlot','boolField':'boolSlot','bytesField':'bytesSlot','read':'callRead','choose':'conditional'}if c else{}
    ctor='FormalSpecAgent.CSubset.'+('CExpr.'if c else'IRExpr.')+names.get(tag,tag)
    if tag=='integer':return '('+ctor+' '+gate.number(args[0])+')'
    if tag=='boolean':return '('+ctor+' '+('true'if args[0]else'false')+')'
    if tag in ('intField','boolField','bytesField'):return '('+ctor+' '+str(args[0])+')'
    return '('+ctor+' '+' '.join(lean_tree(a,c)for a in args)+')'


def prepare(task_file,workspace,task_sha256,*,draft=False):
    root=Path(workspace).resolve();task_file=Path(task_file).resolve()
    if not task_file.is_relative_to(root)or gate.sha(task_file)!=task_sha256:raise ValueError('C task outside workspace or digest mismatch')
    t=json.loads(task_file.read_text())
    keys={'schema','id','model','model_sha256','sources','target','witnesses','lean_version','foundation_sha256','c_semantics_sha256','runtime_sha256','harness_sha256','parser_sha256','c_source','approved_sha256'}
    if set(t)!=keys or t['schema']!='fsa-lean-c-expression-task-v1'or t['lean_version']!=gate.VERSION:raise ValueError('Unsupported C correspondence task')
    if gate.sha(Path(__file__).resolve())!=t['parser_sha256']:raise ValueError('Approved C parser epoch changed')
    if type(t['id'])is not str or not re.fullmatch(r'[A-Za-z0-9_-]{1,80}',t['id']):raise ValueError('Invalid C task identity')
    if gate.sha(HERE/'lean/Foundation.lean')!=t['foundation_sha256']or gate.sha(HERE/'lean/CSubset.lean')!=t['c_semantics_sha256']or gate.sha(RUNTIME)!=t['runtime_sha256']or gate.sha(HARNESS)!=t['harness_sha256']:raise ValueError('C correspondence semantic/runtime epoch changed')
    model_file=gate.inside(root,t['model']);chain=model_files(model_file)
    if gate.sha(model_file)!=t['model_sha256']:raise ValueError('C task model digest mismatch')
    paths=[task_file,*chain];pinned=set()
    if type(t['sources'])is not list or not t['sources']:raise ValueError('Pinned C contract sources required')
    for row in t['sources']:
        if set(row)!={'path','sha256'}:raise ValueError('Invalid C source binding')
        p=gate.inside(root,row['path'])
        if gate.sha(p)!=row['sha256']:raise ValueError('C contract source digest mismatch')
        paths.append(p);pinned.add(p)
    if not set(chain[1:])<=pinned:raise ValueError('Every C task model base must be pinned')
    if set(t['c_source'])!={'path','sha256'}:raise ValueError('Explicit C artifact binding required')
    cfile=gate.inside(root,t['c_source']['path'])
    if gate.sha(cfile)!=t['c_source']['sha256']:raise ValueError('Generated C digest mismatch')
    paths.append(cfile);m=load(model_file)
    if m['ir_version']not in ('0.5','0.6')or m['semantics']!='flat-efsm-atomic-ordered-v1':raise ValueError('Unsupported C-unit IR semantics')
    target=t['target']
    if set(target)!={'rule','action'}or type(target['action'])is not int or target['action']!=0:raise ValueError('C unit currently requires the first assignment action')
    matches=[(i,r)for i,r in enumerate(m['transitions'])if r['id']==target['rule']]
    if len(matches)!=1:raise ValueError('Unknown C target rule')
    ix,r=matches[0]
    if not r['actions']:raise ValueError('Selected rule has no assignment')
    a=r['actions'][0]
    if set(a)!={'set'}or infer(a['set']['value'],m,r['event'])!='int':raise ValueError('Integer assignment required')
    fields=m['events'][r['event']]['fields']
    if not fields or len(fields)>64 or any(k not in ('int','bool','bytes')for k in fields.values()):raise ValueError('Unsupported C context fields')
    original=ir_tree(a['set']['value'],m,r['event']);parsed,view=parse_expression(cfile.read_text(),fields,ix,list(m['variables']).index(a['set']['var']))
    ns='FormalSpecAgent.CSubset.'
    statements={
        'read_model_equivalent':'∀ (xs : FormalSpecAgent.Bytes) (i : Int), '+ns+'cRead xs i = FormalSpecAgent.byteAt xs i',
        'valid_index_bound':'∀ (len : Nat) (i : Int), 0 <= i → i < Int.ofNat len → i.toNat < len',
        'lowering_correct':'∀ (k : '+ns+'Kind) (e : '+ns+'IRExpr k) (ctx : '+ns+'Context), '+ns+'evalC ('+ns+'lower e) ctx = '+ns+'evalIR e ctx',
        'actual_lowering':'actualC = '+ns+'lower originalIR',
        'actual_refines':'∀ (ctx : '+ns+'Context), '+ns+'NativeContext ctx → '+ns+'evalC actualC ctx = '+ns+'evalIR originalIR ctx',
    }
    kinds={'int':'Int','bool':'Bool','bytes':'FormalSpecAgent.Bytes'}
    binders=' '.join('(f'+str(i)+' : '+kinds[k]+')'for i,k in enumerate(fields.values()))
    def selector(kind,default):
        return 'fun n => '+''.join('if n = '+str(i)+' then f'+str(i)+' else 'for i,k in enumerate(fields.values())if k==kind)+default
    env='{ integers := '+selector('int','0')+', booleans := '+selector('bool','false')+', buffers := '+selector('bytes','[]')+' }'
    witnesses=t['witnesses']
    if type(witnesses)is not list or not 1<=len(witnesses)<=32:raise ValueError('C witnesses required')
    nonzero=False
    for w in witnesses:
        if set(w)!={'id','fields','expected'}or not re.fullmatch(r'[a-z][a-z0-9_]{0,50}',w['id']):raise ValueError('Bad C witness schema')
        name='witness_'+w['id']
        if name in statements or set(w['fields'])!=set(fields)or type(w['expected'])is not int:raise ValueError('Bad C witness fields/identity')
        for n,k in fields.items():
            v=w['fields'][n]
            if not value_ok(v,k)or(k=='int'and not -(2**63)<=v<2**63)or(k=='bytes'and len(v)>4096):raise ValueError('C witness outside native domain')
        values=' '.join('('+gate.literal(w['fields'][n],k)+')'for n,k in fields.items())
        if w['expected']!=0 and 'native_context_witness'not in statements:
            statements['native_context_witness']=ns+'NativeContext (environment '+values+')'
        statements[name]=ns+'evalC actualC (environment '+values+') = '+gate.number(w['expected']);nonzero|=w['expected']!=0
    if not nonzero:raise ValueError('Nonzero C witness required')
    approved='import CSubset\n\nnamespace Approved\n\ndef originalIR : '+ns+'IRExpr .integer :=\n  '+lean_tree(original)+'\n\ndef actualC : '+ns+'CExpr .integer :=\n  '+lean_tree(parsed,True)+'\n\ndef environment '+binders+' : '+ns+'Context :=\n  '+env+'\n\n'
    approved+='\n\n'.join('def '+n+' : Prop :=\n  '+s for n,s in statements.items())+'\n\nend Approved\n'
    if not draft and hashlib.sha256(approved.encode()).hexdigest()!=t['approved_sha256']:raise ValueError('C statements differ from frozen approval')
    inputs={'workspace/'+str(p.relative_to(root)):gate.sha(p)for p in paths}
    for p in [Path(__file__).resolve(),HERE/'lean_backend.py',HERE/'lean/Foundation.lean',HERE/'lean/CSubset.lean',HERE/'lean/lean-toolchain']:
        inputs['tool/'+str(p.relative_to(HERE))]=gate.sha(p)
    inputs['ir_checker']=gate.sha(HERE.parent/'protocol_lab/ir.py');inputs['C_runtime']=gate.sha(RUNTIME);inputs['C_harness']=gate.sha(HARNESS)
    # The reified actual tree is included in the approved source, not inferred
    # from the IR or generated as expected native output.
    return approved,list(statements),inputs
