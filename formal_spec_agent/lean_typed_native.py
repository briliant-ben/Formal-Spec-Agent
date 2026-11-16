"""Compile the typed pure IR evaluator with inputs only; compare after exit."""
import json
import os
from pathlib import Path
import shutil
import subprocess

from protocol_lab.ir import load
from . import lean_backend as gate
from .lean_typed import View


def render_runtime(view,inputs):
    data=view.source().replace('namespace Approved\n','namespace ValuesRuntime\n',1)
    runner='''import ModelValues

open FormalSpecAgent.TypedIR

def numbers (xs : List Nat) : String :=
  "[" ++ String.intercalate "," (xs.map toString) ++ "]"

def valueText (k : Kind) (v : Value k) : String :=
  match k with
  | .integer => toString v
  | .boolean => toString v
  | .sequence => toString v.val
  | .octets => numbers (v.map Fin.val)
  | .text => numbers (v.toList.map Char.toNat)

def main : IO Unit := do
'''
    contexts={}
    for i,c in enumerate(inputs):
        if type(c)is not dict or set(c)!={'target','context'}:raise ValueError('Runtime builder accepts inputs only')
        target=view.roots[c['target']];ctx=view.context(c['context'],target['event'])
        if ctx in contexts:body='context_'+str(contexts[ctx])
        else:contexts[ctx]=i;body=ctx
        data+='\ndef context_'+str(i)+' : FormalSpecAgent.TypedIR.Context :=\n  '+body+'\n'
        # Only the authoritative target kind and the frozen input context are
        # compiled. No proposition, expected output or worker proof is imported.
        k={'int':'integer','bool':'boolean','seq32':'sequence','bytes':'octets','string':'text'}[target['kind']]
        expression='valueText .'+k+' (eval ValuesRuntime.e'+str(target['node'])+' ValuesRuntime.context_'+str(i)+')'
        runner+='  IO.println ("{\\\"kind\\\":\\\"'+target['kind']+'\\\",\\\"value\\\":" ++ ('+expression+') ++ "}")\n'
    data+='\nend ValuesRuntime\n'
    return data,runner


def run(task_file,workspace,out,proofs_file,task_sha256,lean='lean'):
    root=Path(workspace).resolve();out=Path(out).resolve();task_file=Path(task_file).resolve()
    if out.exists()or out.is_relative_to(root)or out.is_relative_to(gate.HERE.parent):raise ValueError('Fresh external typed native output required')
    if gate.sha(task_file)!=task_sha256:raise ValueError('Typed native task digest mismatch')
    out.mkdir(parents=True);checked=gate.check(task_file,root,out/'certificate',proofs_file,task_sha256,lean)
    result=dict(schema='fsa-lean-native-reference-v1',status='blocked',scope='Compiled pure typed IR expression interpreter on frozen inputs, with Lean runtime. Not standalone protocol C99, EFSM scheduling or verified native compilation.',runtime='Lean runtime required',compiler_correctness_proved=False,protocol_correctness_proved=False,certificate_sha256=gate.sha(out/'certificate/result.json'),checker_sha256=gate.sha(Path(__file__).resolve()),commands=[])
    def save():
        result['outputs']={str(p.relative_to(out)):gate.sha(p)for p in out.rglob('*')if p.is_file()and p!=out/'result.json'}
        gate.write(out/'result.json',result);return result
    if checked['status']!='checked_typed_expression_contract' or not checked.get('typed_expression_contract_checked'):result.update(classification='certificate_not_checked');return save()
    tool=Path(shutil.which(str(lean))).resolve();leanc=tool.parent/'leanc'
    if not leanc.is_file():result.update(classification='environment');return save()
    t=json.loads(task_file.read_text());view=View(load(gate.inside(root,t['model']))).build();certificate=out/'certificate';project=out/'runtime';project.mkdir()
    for n in ['Foundation','ValueOps','TypedIR']:(project/(n+'.lean')).write_bytes((certificate/(n+'.lean')).read_bytes())
    runtime_inputs=[dict(target=c['target'],context=c['context'])for c in t['cases']]
    data,runner=render_runtime(view,runtime_inputs)
    (project/'ModelValues.lean').write_text(data);(project/'Runner.lean').write_text(runner)
    modules=['Foundation','ValueOps','TypedIR','ModelValues','Runner'];sources={n+'.lean':gate.sha(project/(n+'.lean'))for n in modules}
    temp=out/'compiler-tmp';temp.mkdir();env=dict(PATH=os.defpath,LEAN_PATH=str(project),TMPDIR=str(temp),LANG='C.UTF-8')
    result.update(lean_binary_sha256=gate.sha(tool),leanc_binary_sha256=gate.sha(leanc),lean_version=checked['lean_version'],inputs=checked['inputs'],runtime_sources=sources)
    commands=[[str(tool),'-o',n+'.olean','-c',n+'.c',n+'.lean']for n in modules]+[[str(leanc),*[n+'.c'for n in modules],'-o','lean-reference'],[str(project/'lean-reference')]]
    for i,cmd in enumerate(commands):
        try:
            p=subprocess.run(cmd,cwd=project,env=env,capture_output=True,text=True,timeout=90);stdout,stderr,rc=p.stdout,p.stderr,p.returncode
        except subprocess.TimeoutExpired as e:
            stdout=(e.stdout or b'').decode()if isinstance(e.stdout,bytes)else(e.stdout or'');stderr='Typed native wall-clock timeout';rc=None
        (out/(str(i)+'.stdout')).write_text(stdout);(out/(str(i)+'.stderr')).write_text(stderr)
        result['commands'].append(dict(argv=cmd,returncode=rc,stdout_sha256=gate.sha(out/(str(i)+'.stdout')),stderr_sha256=gate.sha(out/(str(i)+'.stderr'))))
        if rc!=0:result.update(status='fail',classification='resource_unknown'if rc is None else'native_tool_failure');return save()
    # Read outputs/oracles only after the subject has returned. Text uses scalar
    # codepoints so newline/NUL encoding errors cannot disappear in line parsing.
    expected=[dict(kind=view.roots[c['target']]['kind'],value=[ord(ch)for ch in c['expected']]if view.roots[c['target']]['kind']=='string'else c['expected'])for c in t['cases']]
    try:observed=[json.loads(line)for line in stdout.splitlines()]
    except ValueError:observed=None
    result.update(status='native_reference_match'if observed==expected else'fail',observed=observed,expected=expected,comparison='Independent frozen expected values are compared only after exit, never compiled into the subject. Propositions and worker proofs are not linked.')
    try:
        stable=gate.prepare(task_file,root,task_sha256)[2]==checked['inputs']and gate.sha(Path(__file__).resolve())==result['checker_sha256']and all(gate.sha(certificate/n)==h for n,h in checked['sources'].items())and all(gate.sha(project/n)==h for n,h in sources.items())
    except (ValueError,OSError):stable=False
    if not stable:result.update(status='invalidated_inputs',classification='evidence_changed')
    return save()
