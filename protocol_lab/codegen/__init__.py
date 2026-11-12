"""Direct native code generation from an explicitly admitted Protocol IR fragment."""
import hashlib
import json
import re
from pathlib import Path
from ..ir import infer,validate,model_files,load
from ..symbolic import model_hash

HERE=Path(__file__).resolve().parent
KINDS={'int':0,'bool':1,'seq32':2,'bytes':3,'string':4}
BYTE_CAP=4096
OPS={'eq','ne','and','or','not','implies','add','sub','mul','le','ge','min','ite',
     'seq_add','seq_distance','seq_lt','seq_le','seq_comparable','bytes_len','bytes_concat','bytes_slice',
     'bytes_pack8_mod','bytes_pack16be_mod','bytes_pack32be_mod','bytes_internet_checksum16','bytes_at_or_zero'}

class Unsupported(ValueError): pass

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def cstr(s):return '"'+''.join('\\%03o'%b for b in s.encode())+'"'
def integer(n):
    if not -(1<<63)<=n<(1<<63):raise Unsupported('Integer literal outside signed 64-bit backend domain')
    return 'INT64_MIN'if n==-(1<<63)else '(-INT64_C('+str(-n)+'))'if n<0 else 'INT64_C('+str(n)+')'


def string_literals(m):
    values=set()
    def walk(e):
        if type(e)is str:values.add(e)
        elif type(e)is dict and 'args'in e:
            for a in e['args']:walk(a)
    for v in m['variables'].values():
        if v['type']=='string':values.add(v['initial'])
    for r in m['transitions']:
        walk(r['guard'])
        for action in r['actions']:
            kind,p=next(iter(action.items()))
            if kind=='set':walk(p['value'])
            elif kind in ('emit','emit_if'):
                for e in p['fields'].values():walk(e)
            elif kind in ('arm','arm_if'):walk(p['delay_ms'])
            if kind in ('emit_if','arm_if','cancel_if'):walk(p['when'])
    for inv in m['invariants']:walk(inv['assert'])
    return sorted(values)


def admit(m):
    validate(m)
    names=list(m['states'])+list(m['variables'])+list(m['events'])+list(m['timers'])+list(m['messages'])
    names += [r['id']for r in m['transitions']]+[i['id']for i in m['invariants']]+list(m['requirements'])
    if any('\0'in n for n in names):raise Unsupported('NUL in native identity names unsupported')
    if any(len(n.encode())>256 for n in names):raise Unsupported('Native name capacity exceeded')
    if len(m['variables'])>256:raise Unsupported('Native variable capacity exceeded')
    if any(not re.fullmatch(r'[A-Za-z0-9_.:-]+',n)for n in m['events']):raise Unsupported('Event name cannot be represented in line interface')
    if set(m)!={'ir_version','protocol','semantics','scope','states','initial_state','variables','events','timers','messages','requirements','transitions','invariants'}:
        raise Unsupported('Unknown model fields')
    if m['ir_version']not in ('0.1','0.2','0.4','0.5','0.6')or m['semantics']!='flat-efsm-atomic-ordered-v1':
        raise Unsupported('Backend requires IR0.1/0.2/0.4/0.5/0.6 atomic ordered v1; clock-v3/rational unsupported')
    for v in m['variables'].values():
        if set(v)!={'type','initial'}or v['type']not in KINDS:raise Unsupported('Only int/bool/seq32/bytes/closed-string state supported in native-v2')
        if v['type']=='bytes':
            if len(v['initial'])>BYTE_CAP:raise Unsupported('Byte literal exceeds native buffer capacity')
        elif v['type']!='string':integer(v['initial'])
    for spec in m['events'].values():
        if 'string'in spec['fields'].values():raise Unsupported('String event fields unsupported; state strings use source literals only')
        if set(spec)!={'origin','fields'}or any(t not in KINDS for t in spec['fields'].values())or len(spec['fields'])>64:
            raise Unsupported('Unsupported event schema')
        if spec['origin']=='timer'and spec['fields']:raise Unsupported('Timer event fields unsupported')
    for spec in m['messages'].values():
        if set(spec)!={'fields'}or any(t not in (*KINDS,'string')for t in spec['fields'].values()):raise Unsupported('Unsupported message schema')
    if any(set(t)!={'event'}for t in m['timers'].values()):raise Unsupported('Unsupported timer fields')
    def expr(e,depth=0):
        if depth>64:raise Unsupported('Native expression depth capacity exceeded')
        if type(e)is int:integer(e);return
        if type(e)in (str,bool):return
        if type(e)is not dict:raise Unsupported('Unsupported literal')
        if set(e)in ({'var'},{'event'},{'state'},{'timer_active'}):return
        if set(e)=={'bytes'}:
            if len(e['bytes'])>BYTE_CAP:raise Unsupported('Byte literal exceeds native buffer capacity')
            return
        if set(e)=={'seq'}:integer(e['seq']);return
        if set(e)=={'op','args'}and e['op']in OPS:
            for a in e['args']:expr(a,depth+1)
            return
        raise Unsupported('Unsupported expression; clock/rational are not lowered')
    for r in m['transitions']:
        if set(r)!={'id','from','to','event','guard','actions','requirements'}:raise Unsupported('Unsupported rule/target fields')
        expr(r['guard'])
        for a in r['actions']:
            k,p=next(iter(a.items()))
            if k=='set':
                if set(p)!={'var','value'}:raise Unsupported('Extra assignment semantics')
                expr(p['value'])
            elif k in ('emit','emit_if'):
                if set(p)!=({'message','fields','when'}if k=='emit_if'else{'message','fields'}):raise Unsupported('Extra emission semantics')
                if k=='emit_if':expr(p['when'])
                for e in p['fields'].values():expr(e)
            elif k in ('arm','arm_if'):
                if set(p)!=({'timer','delay_ms','when'}if k=='arm_if'else{'timer','delay_ms'}):raise Unsupported('Extra timer semantics')
                expr(p['delay_ms'])
                if k=='arm_if':expr(p['when'])
            elif k=='cancel':pass
            elif k=='cancel_if':
                if set(p)!={'timer','when'}:raise Unsupported('Extra timer semantics')
                expr(p['when'])
            else:raise Unsupported('Unsupported action '+k)
    for inv in m['invariants']:
        if set(inv)!={'id','requirements','assert'}:raise Unsupported('Unsupported invariant fields')
        expr(inv['assert'])


def render(m,wire=None):
    if wire is not None:raise Unsupported("Legacy TCP wire codec is not a generic framework backend")
    admit(m)
    byte_vars=[n for n,v in m['variables'].items()if v['type']=='bytes']
    initial_snapshot=dict(state=m['initial_state'],variables={n:v['initial']for n,v in m['variables'].items()},timers={})
    if len(json.dumps(initial_snapshot,separators=(',',':')).encode())>131072-4096:raise Unsupported('Native initial snapshot capacity exceeded')
    variables=list(m['variables']);events=list(m['events']);timers=list(m['timers']);states=m['states']
    strings=string_literals(m)
    lines=['#define STRING_COUNT '+str(len(strings)),(HERE/'runtime.c').read_text()]
    if wire is not None:
        from .wire import render_codec
        lines.append(render_codec(m,wire))
    emit=lines.append
    def exp(e,event=None):
        if type(e)is bool:return '1'if e else'0'
        if type(e)is int:return integer(e)
        if type(e)is str:return str(strings.index(e))
        if 'bytes'in e:return 'byte_literal((const unsigned char[]){'+(','.join(map(str,e['bytes']))or'0')+'},'+str(len(e['bytes']))+')'
        if 'seq'in e:return integer(e['seq'])
        if 'var'in e:
            name=e['var'];slot='m->b['+str(byte_vars.index(name))+']'if name in byte_vars else'm->v['+str(variables.index(name))+']'
            return slot
        if 'event'in e:
            name=e['event'];ix=str(list(m['events'][event]['fields']).index(name))
            return ('bf['if m['events'][event]['fields'][name]=='bytes'else'f[')+ix+']'
        if 'state'in e:return '(m->state=='+str(states.index(e['state']))+')'
        if 'timer_active'in e:return 'm->active['+str(timers.index(e['timer_active']))+']'
        a=[exp(x,event)for x in e['args']];op=e['op']
        if op in ('eq','ne')and infer(e['args'][0],m,event)=='bytes':return ('(!'if op=='ne'else'(')+'byte_equal('+','.join(a)+'))'
        if op=='bytes_len':return '((int64_t)('+a[0]+').len)'
        if op in ('bytes_concat','bytes_slice'):return {'bytes_concat':'byte_concat','bytes_slice':'byte_slice'}[op]+'('+','.join(a)+')'
        if op in ('bytes_pack8_mod','bytes_pack16be_mod','bytes_pack32be_mod','bytes_internet_checksum16'):
            return {'bytes_pack8_mod':'byte_pack8','bytes_pack16be_mod':'byte_pack16be','bytes_pack32be_mod':'byte_pack32be','bytes_internet_checksum16':'byte_checksum16'}[op]+'('+','.join(a)+')'
        if op=='bytes_at_or_zero':return 'byte_at_or_zero('+','.join(a)+')'
        binary={'eq':'==','ne':'!=','le':'<=','ge':'>=','and':'&&','or':'||'}
        if op in binary:return '('+a[0]+binary[op]+a[1]+')'
        if op=='not':return '(!'+a[0]+')'
        if op=='implies':return '(!'+a[0]+'||'+a[1]+')'
        if op=='ite':return '('+a[0]+'?'+a[1]+':'+a[2]+')'
        if op=='seq_lt':return '(distance('+','.join(a)+')>0&&distance('+','.join(a)+')<INT64_C(2147483648))'
        if op=='seq_le':return '(distance('+','.join(a)+')<INT64_C(2147483648))'
        if op=='seq_comparable':return '(distance('+','.join(a)+')!=INT64_C(2147483648))'
        return {'add':'add','sub':'sub','mul':'mul','min':'minimum','seq_add':'seqadd','seq_distance':'distance'}[op]+'('+','.join(a)+')'
    def literal(out,s):emit('text('+out+','+cstr(s)+');')
    def value(out,e,kind,event=None):
        if kind=='string':emit('text('+out+',source_json('+exp(e,event)+'));')
        elif kind=='bytes':emit('byte_json('+out+','+exp(e,event)+');')
        elif kind=='bool':emit('text('+out+','+exp(e,event)+'?"true":"false");')
        else:emit('number('+out+','+exp(e,event)+');')
    emit('enum { NV='+str(len(variables))+', NB='+str(len(byte_vars))+', NT='+str(len(timers))+' };')
    emit('typedef struct { int state; int64_t now,v[NV?NV:1],due[NT?NT:1]; Bytes b[NB?NB:1]; int active[NT?NT:1]; } Machine;')
    emit('const char *state_names[]={'+','.join(map(cstr,states))+'};')
    emit('const char *event_names[]={'+','.join(map(cstr,events))+'};')
    emit('const char *timer_names[]={'+(','.join(map(cstr,timers))or'""')+'};')
    emit('int event_origin[]={'+','.join('1'if m['events'][e]['origin']=='timer'else'0'for e in events)+'};')
    emit('int event_fields[]={'+','.join(str(len(m['events'][e]['fields']))for e in events)+'};')
    emit('int event_kinds['+str(len(events))+'][FIELD_CAP]={'+','.join('{'+(','.join(str(KINDS[k])for k in m['events'][e]['fields'].values())or'0')+'}'for e in events)+'};')
    emit('int timer_events[]={'+(','.join(str(events.index(m['timers'][t]['event']))for t in timers)or'0')+'};')
    emit('int variable_kinds[]={'+(','.join(str(KINDS[m['variables'][n]['type']])for n in variables)or'0')+'};')
    emit('int variable_byte_index[]={'+(','.join(str(byte_vars.index(n))if n in byte_vars else'-1'for n in variables)or'-1')+'};')
    emit('const char *variable_names[]={'+(','.join(map(cstr,variables))or'""')+'};')
    emit('const char *source_json_strings[]={'+(','.join(cstr(json.dumps(value))for value in strings)or'""')+'};')
    emit('const char *source_json(int64_t i) { if(i<0||i>=STRING_COUNT){failure="string_domain";return '+cstr('""')+';}return source_json_strings[i];}')
    if wire is not None:
        emit('const char *wire_source_string(int64_t i) { switch(i) {')
        for i,wire_literal in enumerate(strings):
            if wire_literal in ('S','SA','A'):emit('case '+str(i)+':return '+cstr(wire_literal)+';')
        emit('default:failure="unsupported_wire_output_flags";return "";} }')
    emit('void initialize(Machine *m) { memset(m,0,sizeof(*m)); m->state='+str(states.index(m['initial_state']))+';')
    for i,n in enumerate(variables):
        initial=m['variables'][n]['initial'];expression={'bytes':initial}if n in byte_vars else initial
        slot='m->b['+str(byte_vars.index(n))+']'if n in byte_vars else'm->v['+str(i)+']'
        initial_c=exp(expression)
        emit(slot+'='+initial_c+';')
    emit('}')
    emit('int invariants(Machine *m) { (void)m; if(failure)return 0;')
    for inv in m['invariants']:emit('if(!('+exp(inv['assert'])+')) {failure='+cstr('invariant:'+inv['id'])+';return 0;}')
    emit('return failure==NULL; }')
    emit('void snapshot(Buffer *out,Machine *m) { int first=1;')
    literal('out','{"state":');emit('switch(m->state) {')
    for i,s in enumerate(states):emit('case '+str(i)+':');literal('out',json.dumps(s));emit('break;')
    emit('default:failure="invalid_state";}');literal('out',',"variables":{')
    for i,n in enumerate(variables):
        literal('out',(','if i else'')+json.dumps(n)+':');value('out',{'var':n},m['variables'][n]['type'])
    literal('out','},"timers":{')
    for i,n in enumerate(timers):
        emit('if(m->active['+str(i)+']) { if(!first)text(out,",");first=0;');literal('out',json.dumps(n)+':');emit('number(out,m->due['+str(i)+']);}')
    emit('(void)first;');literal('out','}}');emit('}')
    # Keep each rule's value-type byte temporaries in its own C stack frame.
    # The dispatcher still evaluates every eligible guard in declaration order
    # before choosing any action, so conflict/error/atomic commit semantics stay
    # in the unchanged command harness. No optimization flags are required.
    for i,r in enumerate(m['transitions']):
        emit('static int rule_guard_'+str(i)+'(Machine *m,int64_t *f,Bytes *bf) { (void)m; (void)f; (void)bf; return '+exp(r['guard'],r['event'])+'; }')
    for i,r in enumerate(m['transitions']):
        ev=r['event'];emit('static int rule_action_'+str(i)+'(Machine *m,int64_t *f,Bytes *bf,Buffer *log) { Buffer messages={{0},0}; int emitted=0; (void)f; (void)bf; (void)emitted;')
        for a in r['actions']:
            k,p=next(iter(a.items()))
            if k=='set':
                name=p['var'];slot='m->b['+str(byte_vars.index(name))+']'if name in byte_vars else'm->v['+str(variables.index(name))+']'
                expression=exp(p['value'],ev)
                emit(slot+'='+expression+';')
            elif k in ('emit','emit_if'):
                emit('if('+exp(p['when'],ev)+') {'if k=='emit_if'else'{')
                emit('if(emitted++)text(&messages,",");');literal('&messages','{"message":'+json.dumps(p['message'])+',"fields":{')
                for j,(name,e)in enumerate(p['fields'].items()):
                    literal('&messages',(','if j else'')+json.dumps(name)+':');value('&messages',e,m['messages'][p['message']]['fields'][name],ev)
                literal('&messages','}}');
                if wire is not None:
                    if p['message']!=wire['message']:raise Unsupported('Wire profile cannot encode another message')
                    f=p['fields'];emit('wire_emit(log,wire_source_string('+exp(f['flags'],ev)+'),'+','.join(exp(f[n],ev)for n in ('seq','ack','window'))+',m->now);')
                emit('}')
            elif k in ('arm','arm_if'):
                emit('if('+exp(p['when'],ev)+') {'if k=='arm_if'else'{');emit('int64_t delay='+exp(p['delay_ms'],ev)+'; if(delay<=0){failure="invalid_timer_delay";return 0;}')
                ix=str(timers.index(p['timer']));emit('m->due['+ix+']=add(m->now,delay);m->active['+ix+']=1;}')
            elif k in ('cancel','cancel_if'):
                name=p if k=='cancel'else p['timer'];condition='1'if k=='cancel'else exp(p['when'],ev)
                emit('if('+condition+')m->active['+str(timers.index(name))+']=0;')
            emit('if(failure)return 0;')
        emit('m->state='+str(states.index(r['to']))+'; if(!invariants(m))return 0;')
        literal('log','{"status":"transition","transition":'+json.dumps(r['id'])+',"requirements":'+json.dumps(r['requirements'])+',"time_ms":');emit('number(log,m->now);')
        literal('log',',"event":{"name":'+json.dumps(ev)+',"fields":{')
        for j,(name,kind)in enumerate(m['events'][ev]['fields'].items()):
            literal('log',(','if j else'')+json.dumps(name)+':');value('log',{'event':name},kind,ev)
        literal('log','}},"after":');emit('snapshot(log,m);');literal('log',',"emitted":[');emit('text(log,messages.data);');literal('log',']}\n');emit('return failure==NULL; }')
    emit('int fire(Machine *m,int event,int64_t *f,Bytes *bf,int expiring,Buffer *log) { int match=-1,count=0;')
    for i,r in enumerate(m['transitions']):
        emit('if(m->state=='+str(states.index(r['from']))+'&&event=='+str(events.index(r['event']))+'&&rule_guard_'+str(i)+'(m,f,bf)) {match='+str(i)+';count++;}')
    emit('if(failure)return 0;\nif(count!=1){failure=count?"rule_conflict":"uncovered_event";return 0;} if(expiring>=0)m->active[expiring]=0; switch(match) {')
    for i in range(len(m['transitions'])):emit('case '+str(i)+':return rule_action_'+str(i)+'(m,f,bf,log);')
    emit('default:failure="invalid_rule";return 0;} }')
    lines.append((HERE/'harness.c').read_text())
    return '\n'.join(lines)+'\n'


def generate(model_file,out,wire_binding_file=None):
    if wire_binding_file is not None:raise Unsupported("Legacy TCP wire codec is not a generic framework backend")
    model_file=Path(model_file).resolve();out=Path(out).resolve()
    if out.exists():raise ValueError('Fresh output directory required')
    paths=model_files(model_file)+[HERE/'__init__.py',HERE/'__main__.py',HERE/'runtime.c',HERE/'harness.c',Path(__file__).parents[1]/'ir.py',Path(__file__).parents[1]/'symbolic.py']
    wire=None
    if wire_binding_file is not None:
        wire_binding_file=Path(wire_binding_file).resolve();wire=json.loads(wire_binding_file.read_text())
        paths += [wire_binding_file,HERE/'wire.py',HERE/'wire.c']
    inputs={str(p):sha(p)for p in paths}
    m=load(model_file);source=render(m,wire)
    if any(sha(p)!=h for p,h in inputs.items()):raise ValueError('Source changed during generation')
    out.mkdir(parents=True);(out/'protocol.c').write_text(source)
    result=dict(schema='spec-flow-stage-v1',stage='generate',status='pass',backend='direct-c99-byte-access-v4',
                model_file=str(model_file),model_semantic_sha256=model_hash(m),inputs=inputs,
                outputs={'protocol.c':sha(out/'protocol.c')},runtime_python_required=False,
                external_protocol_stack_used=False,compiler_correctness_proved=False,
                limits=dict(integer='signed64; checked overflow',command_log_bytes=131072,fields_per_event=64,variables=256,bytes_per_buffer=BYTE_CAP,input_line_bytes=2*BYTE_CAP*64+4096,name_bytes=256,timer_steps_per_command=4096,expression_depth=64,reply_snapshot_reserve_bytes=4096),
                unsupported=['rational','clock-v3','post-action target cases','string event fields','strings outside source-literal domain'],string_domain=string_literals(m),
                rules=[dict(id=r['id'],requirements=r['requirements'])for r in m['transitions']],
                scope=m['scope'])
    if wire is not None:result.update(wire_binding=wire,wire_binding_file=str(wire_binding_file),wire_scope='fixed IPv4/TCP header codec and selected input shape; not full IPv4 behavior')
    (out/'generation.json').write_text(json.dumps(result,indent=2)+'\n');return result
