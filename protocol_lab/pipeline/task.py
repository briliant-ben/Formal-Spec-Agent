import hashlib
import json
from pathlib import Path
import re

TOOL=Path(__file__).resolve().parents[1]
SCHEMA='spec-flow-task-v2'
SCHEMAS={'spec-flow-task-v1',SCHEMA,'spec-flow-task-v3','spec-flow-task-v4','spec-flow-task-v5'}


def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def write(p,v):Path(p).write_text(json.dumps(v,indent=2,ensure_ascii=False)+'\n')


def resolve(workspace,name):
    if not isinstance(name,str):raise ValueError('Input path must be a string')
    path=(Path(workspace)/name).resolve()
    if not path.is_relative_to(Path(workspace).resolve()):raise ValueError('Input path escapes workspace')
    if not path.is_file():raise ValueError('Input file unavailable: '+name)
    return path


def load_task(filename,workspace):
    workspace=Path(workspace).resolve();filename=Path(filename).resolve()
    if not filename.is_relative_to(workspace):raise ValueError('Task outside workspace')
    t=read(filename)
    if 'wire' in t:raise ValueError('Legacy TCP wire binding belongs to the TCPIP benchmark; use IR byte outputs or an external observation adapter')
    keys={'schema','id','model','sources','requirement_bindings','exploration','seeds','formal','limits','scope'}
    if t.get('schema')=='spec-flow-task-v3':keys.add('wire')
    if set(t)!=keys or t['schema']not in SCHEMAS:raise ValueError('Unknown task fields/version')
    if not isinstance(t['id'],str)or not re.fullmatch(r'[A-Za-z0-9_.-]+',t['id']):raise ValueError('Invalid task ID')
    names=[t['model'],t['exploration'],*t['seeds'],*(s['path']for s in t['sources'])]
    if 'wire'in t:
        w=t['wire']
        if set(w)!={'binding','scenarios'}or not isinstance(w['scenarios'],list)or not w['scenarios']:raise ValueError('Explicit wire binding/scenarios required')
        names += [w['binding'],*w['scenarios']]
    if any(Path(n).is_absolute()for n in names):raise ValueError('Task input paths must be relative to workspace')
    resolve(workspace,t['model']);resolve(workspace,t['exploration'])
    if not isinstance(t['seeds'],list):raise ValueError('Seeds must be a list')
    for name in t['seeds']:resolve(workspace,name)
    if not isinstance(t['sources'],list)or not t['sources']:raise ValueError('Pinned sources required')
    ids=[]
    for s in t['sources']:
        if set(s)!={'id','path','sha256','version','uri_aliases'}or not isinstance(s['version'],str)or not s['version']:raise ValueError('Incomplete source declaration')
        if not isinstance(s['id'],str)or not re.fullmatch(r'[A-Za-z0-9_.-]+',s['id']):raise ValueError('Invalid source ID')
        resolve(workspace,s['path']);ids.append(s['id'])
        if not re.fullmatch('[0-9a-f]{64}',s['sha256']):raise ValueError('Invalid source digest')
        if not isinstance(s['uri_aliases'],list)or not s['uri_aliases']or any(not isinstance(u,str)or not u for u in s['uri_aliases']):raise ValueError('Source URI aliases required')
    if len(ids)!=len(set(ids)):raise ValueError('Duplicate source ID')
    if t['schema']in ('spec-flow-task-v2','spec-flow-task-v3','spec-flow-task-v4','spec-flow-task-v5'):
        pinned={resolve(workspace,s['path'])for s in t['sources']}
        required={resolve(workspace,t['exploration']),*(resolve(workspace,n)for n in t['seeds'])}
        if 'wire'in t:required|={resolve(workspace,t['wire']['binding']),*(resolve(workspace,n)for n in t['wire']['scenarios'])}
        if not required<=pinned:raise ValueError('Task v2 must pin every seed and exploration input')
    if not isinstance(t['requirement_bindings'],dict):raise ValueError('Requirement bindings required')
    for b in t['requirement_bindings'].values():
        if set(b)!={'source','clause','reference'}or b['source']not in ids or any(not isinstance(b[k],str)or not b[k]for k in b):raise ValueError('Incomplete requirement binding')
    f=t['formal'];limits=t['limits']
    if t['schema']=='spec-flow-task-v5':
        if set(f)-{'strategy','solver_timeout_ms'} or f.get('strategy')!='initial-step-contracts':raise ValueError('Unsupported v5 formal strategy/configuration')
    elif t['schema']=='spec-flow-task-v4':
        if 'solver_preprocess' in f:raise ValueError('BMC solver preprocessing is not valid for sequence induction')
        if set(f)not in ({'strategy'},{'strategy','solver_timeout_ms'})or f.get('strategy')!='sequence-invariant-induction':raise ValueError('Unsupported v4 formal strategy/configuration')
    else:
        allowed={'depth','symbolic_initials','solver_timeout_ms','solver_preprocess'}
        required={'depth','symbolic_initials'}
        if set(f)-allowed or not required<=set(f) or type(f['depth'])is not int or not 1<=f['depth']<=30 or not isinstance(f['symbolic_initials'],list):raise ValueError('Unsupported formal configuration')
        if f.get('solver_preprocess','none')not in ('none','exact-v1'):raise ValueError('Unsupported formal solver preprocessing plan')
    budget=f.get('solver_timeout_ms',10000)
    if type(budget)is not int or not 100<=budget<=60000:raise ValueError('Invalid solver time budget')
    if set(limits)!={'stage_seconds','max_prefixes','max_cases'}or any(type(n)is not int for n in limits.values()):raise ValueError('Invalid resource limits')
    if not 1<=limits['stage_seconds']<=600 or not 1<=limits['max_prefixes']<=10000 or not 1<=limits['max_cases']<=1000:raise ValueError('Resource budget outside admitted range')
    if not isinstance(t['scope'],dict)or set(t['scope'])!={'purpose','assumptions','excluded'}:raise ValueError('Explicit task scope required')
    return t


def inputs(filename,workspace,t):
    from ..ir import model_files
    workspace=Path(workspace).resolve()
    paths=[Path(filename).resolve(),resolve(workspace,t['exploration'])]
    paths+=model_files(resolve(workspace,t['model']))
    paths+=[resolve(workspace,s['path'])for s in t['sources']]
    paths+=[resolve(workspace,s)for s in t['seeds']]
    if any(not p.is_relative_to(workspace)for p in paths):raise ValueError('Resolved model chain escapes workspace')
    result={'workspace/'+p.relative_to(workspace).as_posix():sha(p)for p in paths}
    for p in sorted(TOOL.rglob('*')):
        if p.is_file()and p.suffix in ('.py','.c'):result['tool/'+p.relative_to(TOOL).as_posix()]=sha(p)
    return result


def check_inputs(snapshot,workspace,tool_root=TOOL):
    tool_root=Path(tool_root).resolve()
    expected={n for n in snapshot if n.startswith('tool/')}
    actual={'tool/'+p.relative_to(tool_root).as_posix()for p in tool_root.rglob('*')if p.is_file()and p.suffix in ('.py','.c')}
    if expected!=actual:raise ValueError('Tool source file set changed')
    for name,h in snapshot.items():
        prefix,tail=name.split('/',1);root=Path(workspace).resolve()if prefix=='workspace'else tool_root if prefix=='tool'else None
        if root is None:raise ValueError('Unknown input namespace')
        path=(root/tail).resolve()
        if not path.is_relative_to(root)or sha(path)!=h:raise ValueError('Source input changed: '+name)


def freeze_inputs(snapshot,workspace,out):
    roots={'workspace':Path(workspace).resolve(),'tool':TOOL}
    targets={'workspace':Path(out)/'source-snapshot/workspace',
             'tool':Path(out)/'source-snapshot/tool/protocol_lab'}
    files={}
    for name,h in snapshot.items():
        prefix,tail=name.split('/',1);source=(roots[prefix]/tail).resolve()
        if not source.is_relative_to(roots[prefix]):raise ValueError('Snapshot source escapes input root')
        raw=source.read_bytes()
        if hashlib.sha256(raw).hexdigest()!=h:raise ValueError('Input changed while freezing: '+name)
        target=targets[prefix]/tail;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(raw);target.chmod(0o444)
        files[name]=target.relative_to(out).as_posix()
    return dict(workspace='source-snapshot/workspace',tool='source-snapshot/tool/protocol_lab',files=files)
