"""Optional Lean-to-C reference execution of a checked pure IR expression."""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

from protocol_lab.ir import load
from . import lean_backend as gate


def run(task_file,workspace,out,proofs_file,task_sha256,lean='lean'):
    root=Path(workspace).resolve();out=Path(out).resolve();task_file=Path(task_file).resolve()
    if out.exists()or out.is_relative_to(root)or out.is_relative_to(gate.HERE.parent):raise ValueError('Fresh external native-reference output required')
    if gate.sha(task_file)!=task_sha256:raise ValueError('Native-reference task digest mismatch')
    t=json.loads(task_file.read_text())
    if t.get('schema')=='fsa-lean-typed-expression-task-v1':
        from .lean_typed_native import run as typed_run
        return typed_run(task_file,root,out,proofs_file,task_sha256,lean)
    if t.get('schema')!='fsa-lean-c-expression-task-v1':raise ValueError('Native-reference pilot requires the C-expression task')
    out.mkdir(parents=True)
    checked=gate.check(task_file,root,out/'certificate',proofs_file,task_sha256,lean)
    result=dict(schema='fsa-lean-native-reference-v1',status='blocked',scope='Compiled Lean interpreter of the selected pure IR expression on frozen witnesses. Not a standalone C99 protocol implementation or verified native compiler.',runtime='Lean runtime required',compiler_correctness_proved=False,protocol_correctness_proved=False,certificate_sha256=gate.sha(out/'certificate/result.json'),checker_sha256=gate.sha(Path(__file__).resolve()),commands=[])
    def save():
        result['outputs']={str(p.relative_to(out)):gate.sha(p)for p in out.rglob('*')if p.is_file()and p!=out/'result.json'}
        gate.write(out/'result.json',result);return result
    if checked['status']!='checked_expression_contract' or not checked.get('c_expression_model_refinement_checked'):
        result.update(classification='certificate_not_checked');return save()
    tool=Path(shutil.which(str(lean))).resolve();leanc=tool.parent/'leanc'
    if not leanc.is_file():result.update(classification='environment',reason='Matching Lean C compiler driver unavailable');return save()
    certificate=out/'certificate';project=out/'runtime';project.mkdir()
    for n in ['Foundation','CSubset','Approved']:(project/(n+'.lean')).write_bytes((certificate/(n+'.lean')).read_bytes())
    m=load(gate.inside(root,t['model']));r=next(r for r in m['transitions']if r['id']==t['target']['rule']);fields=m['events'][r['event']]['fields']
    runner='import Approved\n\ndef main : IO Unit := do\n'
    for w in t['witnesses']:
        args=' '.join('('+gate.literal(w['fields'][n],k)+')'for n,k in fields.items())
        runner+='  IO.println (FormalSpecAgent.CSubset.evalIR Approved.originalIR (Approved.environment '+args+'))\n'
    (project/'Runner.lean').write_text(runner)
    temporary=out/'compiler-tmp';temporary.mkdir()
    env=dict(PATH=os.defpath,LEAN_PATH=str(project),LANG='C.UTF-8',TMPDIR=str(temporary))
    result.update(lean_binary_sha256=gate.sha(tool),leanc_binary_sha256=gate.sha(leanc),lean_version=checked['lean_version'],inputs=checked['inputs'])
    runtime_sources={p.name:gate.sha(p)for p in project.glob('*.lean')};result['runtime_sources']=runtime_sources
    commands=[[str(tool),'-o',n+'.olean','-c',n+'.c',n+'.lean']for n in ['Foundation','CSubset','Approved','Runner']]
    commands.append([str(leanc),'Foundation.c','CSubset.c','Approved.c','Runner.c','-o','lean-reference'])
    commands.append([str(project/'lean-reference')])
    for index,cmd in enumerate(commands):
        try:
            p=subprocess.run(cmd,cwd=project,env=env,capture_output=True,text=True,timeout=90)
            stdout,stderr,rc=p.stdout,p.stderr,p.returncode
        except subprocess.TimeoutExpired as e:
            stdout=(e.stdout or b'').decode()if isinstance(e.stdout,bytes)else(e.stdout or'');stderr='native reference wall-clock timeout';rc=None
        (out/(str(index)+'.stdout')).write_text(stdout);(out/(str(index)+'.stderr')).write_text(stderr)
        result['commands'].append(dict(argv=cmd,returncode=rc,stdout_sha256=gate.sha(out/(str(index)+'.stdout')),stderr_sha256=gate.sha(out/(str(index)+'.stderr'))))
        if rc!=0:result.update(status='fail',classification='resource_unknown'if rc is None else'native_tool_failure');return save()
    expected=[w['expected']for w in t['witnesses']]
    try:observed=[int(line)for line in stdout.splitlines()]
    except ValueError:observed=None
    result.update(status='native_reference_match'if observed==expected else'fail',observed=observed,expected=expected,comparison='Frozen expected values are read only after the executable has returned; they are never sent to it.')
    try:
        stable=gate.prepare(task_file,root,task_sha256)[2]==checked['inputs'] and gate.sha(Path(__file__).resolve())==result['checker_sha256'] and all(gate.sha(certificate/n)==h for n,h in checked['sources'].items()) and all(gate.sha(project/n)==h for n,h in runtime_sources.items())
    except (ValueError,OSError):
        stable=False
    if not stable:
        result.update(status='invalidated_inputs',classification='evidence_changed')
    return save()


def main(argv=None):
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('task',type=Path);p.add_argument('--workspace',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--proofs',type=Path,required=True);p.add_argument('--task-sha256',required=True);p.add_argument('--lean',default='lean')
    a=p.parse_args(argv)
    try:
        r=run(a.task,a.workspace,a.out,a.proofs,a.task_sha256,a.lean);print(json.dumps(r));return 0 if r['status']=='native_reference_match'else 1
    except (ValueError,OSError,subprocess.SubprocessError)as e:
        print(json.dumps(dict(status='rejected',reason=str(e))),file=sys.stderr);return 2
