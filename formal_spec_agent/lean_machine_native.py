"""Execute input-only typed IR microsteps compiled by Lean; compare after exit."""
import argparse
import json
import os
import re
import sys
from pathlib import Path
import shutil
import subprocess

from protocol_lab.ir import load
from . import lean_backend as gate
from .lean_machine import MachineView, MODULES


SERIALIZER='''import ModelMachine
open FormalSpecAgent.MachineObserve

def array (xs : List String) : String := "[" ++ String.intercalate "," xs ++ "]"
def pvalue : Packed → String
  | .integer v => "{\\\"kind\\\":\\\"int\\\",\\\"value\\\":" ++ toString v ++ "}"
  | .boolean v => "{\\\"kind\\\":\\\"bool\\\",\\\"value\\\":" ++ toString v ++ "}"
  | .text v => "{\\\"kind\\\":\\\"string\\\",\\\"value\\\":" ++ array (v.toList.map fun c => toString c.toNat) ++ "}"
  | .octets v => "{\\\"kind\\\":\\\"bytes\\\",\\\"value\\\":" ++ array (v.map fun b => toString b.val) ++ "}"
  | .sequence v => "{\\\"kind\\\":\\\"seq32\\\",\\\"value\\\":" ++ toString v ++ "}"
def ss (s : SeenSnapshot) : String :=
  "{\\\"state\\\":" ++ toString s.state ++ ",\\\"now_ms\\\":" ++ toString s.now ++
  ",\\\"variables\\\":" ++ array (s.values.map pvalue) ++ ",\\\"timers\\\":" ++
  array (s.timers.map fun (n,t) => array [toString n,toString t]) ++ "}"
def msg (m : SeenMessage) : String :=
  "{\\\"message\\\":" ++ toString m.1 ++ ",\\\"fields\\\":" ++
  array (m.2.map fun (n,v) => array [toString n,pvalue v]) ++ "}"
def faultName : FormalSpecAgent.TypedMachine.Fault → String
  | .uncovered => "uncovered" | .conflict => "conflict" | .badDelay => "badDelay"
  | .invariant => "invariant" | .time => "time" | .timerInjection => "timerInjection"
  | .pendingTimer => "pendingTimer" | .noTimer => "noTimer"
def outcomeText : Outcome → String
  | .success r e s emitted => "{\\\"status\\\":\\\"ok\\\",\\\"rule\\\":" ++ toString r ++
      ",\\\"event\\\":" ++ toString e ++ ",\\\"after\\\":" ++ ss s ++
      ",\\\"emitted\\\":" ++ array (emitted.map msg) ++ "}"
  | .error f s => "{\\\"status\\\":\\\"error\\\",\\\"fault\\\":\\\"" ++ faultName f ++
      "\\\",\\\"after\\\":" ++ ss s ++ ",\\\"emitted\\\":[]}"

def main : IO Unit := do
'''


def render_runtime(view,cases):
    if type(cases)is not list or not 1<=len(cases)<=128:raise ValueError('Input-only scheduled cases required')
    source=view.source().replace('namespace Approved\n','namespace MachineRuntime\n',1)+'\nend MachineRuntime\n'
    runner=SERIALIZER;rows=0
    for i,c in enumerate(cases):
        if type(c)is not dict or set(c)!={'id','initial','steps'}or type(c['id'])is not str or type(c['steps'])is not list or not 1<=len(c['steps'])<=128:raise ValueError('Runtime cases accept initial/operations only')
        before='s_'+str(i)+'_0';runner+='  let '+before+' := '+view.snapshot(c['initial'])+'\n'
        for j,step in enumerate(c['steps']):
            result='r_'+str(i)+'_'+str(j);command=view.command(step,before).replace(' model ',' MachineRuntime.model ')
            runner+='  let '+result+' := '+command+'\n'
            runner+='  IO.println (outcomeText (outcome MachineRuntime.schema '+before+' '+result+'))\n'
            after='s_'+str(i)+'_'+str(j+1);runner+='  let '+after+' := FormalSpecAgent.TypedMachine.rollback '+before+' '+result+'\n';before=after;rows+=1
    if rows>512:raise ValueError('Runtime scheduled trace resource limit exceeded')
    return source,runner


def input_cases(cases):
    return [dict(id=c['id'],initial=c['initial'],steps=[{k:v for k,v in s.items()if k!='expected'}for s in c['steps']])for c in cases]


def expected_values(view,cases):
    def val(v,k):return dict(kind=k,value=[ord(c)for c in v]if k=='string'else v)
    def snap(s):
        view.snapshot(s)
        return dict(state=view.v.states.index(s['state']),now_ms=s['now_ms'],variables=[val(s['variables'][n],v['type'])for n,v in view.m['variables'].items()],timers=[[view.timers.index(n),s['timers'][n]]for n in view.timers if n in s['timers']])
    rows=[]
    for c in cases:
        before=c['initial']
        for step in c['steps']:
            e=step['expected'];view.expected(e,view.snapshot(before),step)
            if e['status']=='error':rows.append(dict(status='error',fault=e['fault'],after=snap(before),emitted=[]));continue
            r=next(i for i,r in enumerate(view.m['transitions'])if r['id']==e['rule']);messages=[]
            for message in e['emitted']:
                schema=view.m['messages'][message['message']]['fields'];fields=[[i,val(message['fields'][n],k)]for i,(n,k)in enumerate(schema.items())]
                messages.append(dict(message=view.messages.index(message['message']),fields=fields))
            rows.append(dict(status='ok',rule=r,event=view.events.index(view.m['transitions'][r]['event']),after=snap(e['after']),emitted=messages));before=e['after']
    return rows


def run(model_file,workspace,cases_file,out,model_sha256,cases_sha256,lean='lean'):
    root=Path(workspace).resolve();out=Path(out).resolve();model_file=Path(model_file).resolve();cases_file=Path(cases_file).resolve()
    if out.exists()or out.is_relative_to(root)or out.is_relative_to(gate.HERE.parent):raise ValueError('Fresh external machine reference output required')
    if not model_file.is_relative_to(root)or not cases_file.is_relative_to(root)or gate.sha(model_file)!=model_sha256 or gate.sha(cases_file)!=cases_sha256:raise ValueError('Machine execution input pins differ')
    from protocol_lab.ir import model_files
    chain=model_files(model_file)
    if any(not p.is_relative_to(root)for p in chain):raise ValueError('Machine model base escapes workspace')
    view=MachineView(load(model_file));cases=json.loads(cases_file.read_text());source,runner=render_runtime(view,input_cases(cases))
    # Validate expected shape before execution, but never pass its values to the
    # builder. Actual comparison is deliberately deferred until after exit.
    expected_values(view,cases)
    inputs={str(p):gate.sha(p)for p in [*chain,cases_file,Path(__file__).resolve(),gate.HERE/'lean_machine.py',gate.HERE/'lean_typed.py',gate.HERE/'lean_backend.py',gate.HERE.parent/'protocol_lab/ir.py']}
    for n in MODULES:inputs[str(gate.HERE/('lean/'+n+'.lean'))]=gate.sha(gate.HERE/('lean/'+n+'.lean'))
    out.mkdir();runtime=out/'runtime';runtime.mkdir()
    for n in MODULES:(runtime/(n+'.lean')).write_bytes((gate.HERE/('lean/'+n+'.lean')).read_bytes())
    (runtime/'ModelMachine.lean').write_text(source);(runtime/'Runner.lean').write_text(runner);sources={p.name:gate.sha(p)for p in runtime.glob('*.lean')}
    result=dict(schema='fsa-lean-machine-reference-v1',status='incomplete',inputs=inputs,sources=sources,commands=[],scope='Compiled mathematical IR interpreter on frozen explicitly scheduled inputs; requires Lean runtime. Not batch dispatch/tick, whole-EFSM safety or native/compiler/protocol proof.',kernel_literal_contract_checked=False,efsm_safety_proved=False,compiler_correctness_proved=False,protocol_correctness_proved=False)
    def save():result['outputs']={str(p.relative_to(out)):gate.sha(p)for p in out.rglob('*')if p.is_file()and p!=out/'result.json'};gate.write(out/'result.json',result);return result
    tool=shutil.which(str(lean))
    if tool is None:result.update(status='blocked',classification='environment');return save()
    tool=Path(tool).resolve();leanc=tool.parent/'leanc'
    if not leanc.is_file():result.update(status='blocked',classification='environment');return save()
    version=subprocess.run([str(tool),'--version'],capture_output=True,text=True,timeout=10)
    if version.returncode or not re.search(r'\b'+re.escape(gate.VERSION)+r'\b',version.stdout):result.update(status='blocked',classification='tool_version');return save()
    result.update(lean_version=version.stdout.strip(),lean_binary_sha256=gate.sha(tool),leanc_binary_sha256=gate.sha(leanc))
    temp=out/'compiler-tmp';temp.mkdir();env=dict(PATH=os.defpath,LEAN_PATH=str(runtime),TMPDIR=str(temp),LANG='C.UTF-8')
    modules=[*MODULES,'ModelMachine','Runner'];cmds=[[str(tool),'-o',n+'.olean','-c',n+'.c',n+'.lean']for n in modules]+[[str(leanc),*[n+'.c'for n in modules],'-o','lean-machine'],[str(runtime/'lean-machine')]]
    for i,cmd in enumerate(cmds):
        try:x=subprocess.run(cmd,cwd=runtime,env=env,capture_output=True,text=True,timeout=120);stdout,stderr,rc=x.stdout,x.stderr,x.returncode
        except subprocess.TimeoutExpired as e:stdout=(e.stdout or b'').decode()if isinstance(e.stdout,bytes)else(e.stdout or'');stderr='Scheduled runtime wall-clock timeout';rc=None
        (out/(str(i)+'.stdout')).write_text(stdout);(out/(str(i)+'.stderr')).write_text(stderr);result['commands'].append(dict(argv=cmd,returncode=rc,stdout_sha256=gate.sha(out/(str(i)+'.stdout')),stderr_sha256=gate.sha(out/(str(i)+'.stderr'))))
        if rc!=0:result.update(status='fail',classification='resource_unknown'if gate.resource_failure(rc,stdout,stderr)else'native_tool_failure');return save()
    try:observed=[json.loads(line)for line in stdout.splitlines()]
    except ValueError:observed=None
    expected=expected_values(view,cases);result.update(status='scheduled_reference_match'if observed==expected else'fail',observed=observed,expected=expected,comparison='All stored variables/timers, selected rule/event, outputs and error rollback are compared after subject exit; no expected outcome is compiled into the subject.')
    if any(gate.sha(p)!=h for p,h in inputs.items())or any(gate.sha(runtime/n)!=h for n,h in sources.items()):result.update(status='invalidated_inputs',classification='evidence_changed')
    return save()


def main(argv=None):
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('model',type=Path);p.add_argument('--workspace',type=Path,required=True);p.add_argument('--cases',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--model-sha256',required=True);p.add_argument('--cases-sha256',required=True);p.add_argument('--lean',default='lean');a=p.parse_args(argv)
    try:r=run(a.model,a.workspace,a.cases,a.out,a.model_sha256,a.cases_sha256,a.lean);print(json.dumps(r));return 0 if r['status']=='scheduled_reference_match'else 1
    except (ValueError,TypeError,KeyError,OSError,subprocess.SubprocessError)as e:print(json.dumps(dict(status='rejected',reason=str(e))),file=sys.stderr);return 2
