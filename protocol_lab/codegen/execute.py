"""Build and observe generated native code; compare separately with reference IR.

No reference outputs are fed to the native program. This gate does not claim a
network capture, an independent specification, or a proof of the generator.
"""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
from . import generate,render,sha,string_literals
from ..ir import load,value_ok,ModelError
from ..symbolic import model_hash
from ..flow import run_scenario


def write(p,v):Path(p).write_text(json.dumps(v,indent=2)+'\n')

def build(generation,out):
    generation=Path(generation).resolve();out=Path(out).resolve()
    if out.exists():raise ValueError('Fresh build directory required')
    r=json.loads((generation/'generation.json').read_text())
    if r['stage']!='generate'or r['status']!='pass'or r['backend']!='direct-c99-byte-access-v4':raise ValueError('Unsupported generation evidence')
    for name,digest in r['inputs'].items():
        if sha(name)!=digest:raise ValueError('Generation input changed: '+name)
    if sha(generation/'protocol.c')!=r['outputs']['protocol.c']:raise ValueError('Generated source hash changed')
    if ('wire_binding'in r)!=('wire_binding_file'in r):raise ValueError('Incomplete wire binding evidence')
    if 'wire_binding'in r and json.loads(Path(r['wire_binding_file']).read_text())!=r['wire_binding']:raise ValueError('Wire binding differs from source')
    if render(load(r['model_file']),r.get('wire_binding'))!=(generation/'protocol.c').read_text():raise ValueError('Generated source differs from actual IR lowering')
    out.mkdir(parents=True);cc=shutil.which('cc')
    result=dict(schema='spec-flow-stage-v1',stage='compile',status='blocked'if not cc else'incomplete',
                classification='environment',generation_sha256=sha(generation/'generation.json'),
                generated_source_sha256=sha(generation/'protocol.c'))
    if not cc:
        write(out/'compile.json',result);return result
    compiler_before=sha(Path(cc).resolve())
    source_before=sha(generation/'protocol.c')
    command=[cc,'-std=c99','-Wall','-Wextra','-Werror',str(generation/'protocol.c'),'-o',str(out/'protocol-native')]
    p=subprocess.run(command,capture_output=True,text=True,timeout=60)
    (out/'compiler.stdout').write_text(p.stdout);(out/'compiler.stderr').write_text(p.stderr)
    result.update(status='pass'if p.returncode==0 else'fail',classification=None if p.returncode==0 else'code_generation_defect',
                  command=command,returncode=p.returncode,compiler=cc,compiler_sha256=sha(Path(cc).resolve()),
                  compiler_version=subprocess.check_output([cc,'--version'],text=True))
    result['checker_sha256']=sha(__file__)
    if p.returncode==0:result['executable_sha256']=sha(out/'protocol-native')
    if source_before!=sha(generation/'protocol.c')or compiler_before!=sha(Path(cc).resolve())or any(sha(n)!=h for n,h in r['inputs'].items()):
        result.update(status='invalid',classification='evidence_changed')
    write(out/'compile.json',result);return result


def token(value,kind):return 'b:'+bytes(value).hex()if kind=='bytes'else str(int(value))


def commands(model,scenario):
    variables=list(model['variables']);rows=[]
    for name,v in scenario.get('initial',{}).items():
        if name not in variables or not value_ok(v,model['variables'][name]['type']):raise ValueError('Invalid initial override')
        if model['variables'][name]['type']=='string':
            if v not in string_literals(model):raise ValueError('Initial string outside source-literal backend domain')
            value=str(string_literals(model).index(v))
        else:value=token(v,model['variables'][name]['type'])
        rows.append('I '+str(variables.index(name))+' '+value)
    rows.append('B')
    for step in scenario['steps']:
        if type(step['at_ms'])is not int:raise ValueError('Integer milliseconds required')
        if step.get('tick'):rows.append('T '+str(step['at_ms']));continue
        event=step['event'];schema=model['events'][event]['fields'];fields=step.get('fields',{})
        if set(fields)!=set(schema)or any(not value_ok(fields[n],kind)for n,kind in schema.items()):raise ValueError('Invalid event fields')
        rows.append('D '+str(step['at_ms'])+' '+event+''.join(' '+token(fields[n],schema[n])for n in schema))
    if 'settle_ms'in scenario:rows.append('T '+str(scenario['settle_ms']))
    return '\n'.join(rows)+'\n'


def compare(model,scenario,observed):
    # Reference runs only after the native process has produced its observations.
    reference=run_scenario(model,scenario)
    keys=('transition','requirements','time_ms','event','after','emitted')
    expected=[{k:r[k]for k in keys}for r in reference.trace]
    actual=[{k:r[k]for k in keys}for r in observed if r['status']=='transition']
    errors=[r for r in observed if r['status']=='error']
    final=observed[-1].get('snapshot')if observed else None
    differences=[]
    if expected!=actual:differences.append(dict(kind='transition_trace',expected=expected,observed=actual))
    if final!=reference.snapshot():differences.append(dict(kind='final_snapshot',expected=reference.snapshot(),observed=final))
    if errors:differences.append(dict(kind='native_rejection',observed=errors))
    return dict(status='match'if not differences else'different',differences=differences,
                transitions_compared=len(expected),reference_trace=expected,reference_snapshot=reference.snapshot(),
                scope='exact fixed-input trace and snapshot correspondence; not generator correctness or wire evidence')


def run(generation,compiled,scenario_file,out):
    generation=Path(generation).resolve();compiled=Path(compiled).resolve();out=Path(out).resolve()
    if out.exists():raise ValueError('Fresh execution directory required')
    g=json.loads((generation/'generation.json').read_text());c=json.loads((compiled/'compile.json').read_text())
    if c['status']!='pass'or c['generation_sha256']!=sha(generation/'generation.json')or sha(compiled/'protocol-native')!=c['executable_sha256']:raise ValueError('Executable/generation evidence changed')
    if sha(generation/'protocol.c')!=g['outputs']['protocol.c']or c['generated_source_sha256']!=g['outputs']['protocol.c']:raise ValueError('Generated source changed after compilation')
    for name,h in g['inputs'].items():
        if sha(name)!=h:raise ValueError('Source changed since generation')
    model=load(g['model_file']);scenario_file=Path(scenario_file).resolve();scenario=json.loads(scenario_file.read_text())
    data=commands(model,scenario);out.mkdir(parents=True);(out/'native-input.txt').write_text(data)
    inputs={str(scenario_file):sha(scenario_file),str(generation/'generation.json'):sha(generation/'generation.json'),str(compiled/'compile.json'):sha(compiled/'compile.json'),str(Path(__file__).resolve()):sha(__file__),str(Path(__file__).parents[1]/'flow.py'):sha(Path(__file__).parents[1]/'flow.py')}
    p=subprocess.run([str(compiled/'protocol-native')],input=data,capture_output=True,text=True,timeout=30)
    (out/'native.stdout').write_text(p.stdout);(out/'native.stderr').write_text(p.stderr)
    result=dict(schema='spec-flow-stage-v1',stage='execute_compare',status='incomplete',
                model_semantic_sha256=model_hash(model),scenario=scenario['id'],inputs=inputs,
                executable_sha256=sha(compiled/'protocol-native'),native_returncode=p.returncode,
                observation_origin='generated_native_execution',python_interpreter_in_native_process=False,
                linux_network_evidence=False,pcap_evidence=False,whole_protocol_proved=False)
    try:
        observed=[json.loads(line)for line in p.stdout.splitlines()]
        difference=compare(model,scenario,observed);write(out/'difference.json',difference)
        result.update(status='pass'if difference['status']=='match'and p.returncode==0 and not p.stderr else'fail',
                      classification=None if difference['status']=='match'and p.returncode==0 and not p.stderr else'implementation_difference')
    except (ValueError,KeyError,ModelError)as e:
        result.update(status='fail',classification='reference_rejection'if isinstance(e,ModelError)else'invalid_observation',reason=str(e))
    if any(sha(n)!=h for n,h in inputs.items())or any(sha(n)!=h for n,h in g['inputs'].items())or sha(compiled/'protocol-native')!=result['executable_sha256']:
        result.update(status='invalid',classification='evidence_changed')
    result['outputs']={p.name:sha(p)for p in out.iterdir()if p.is_file()}
    write(out/'execution.json',result);return result


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);sub=p.add_subparsers(dest='stage',required=True)
    b=sub.add_parser('build');b.add_argument('generation',type=Path);b.add_argument('--out',required=True,type=Path)
    r=sub.add_parser('run');r.add_argument('generation',type=Path);r.add_argument('--compiled',required=True,type=Path);r.add_argument('--scenario',required=True,type=Path);r.add_argument('--out',required=True,type=Path)
    a=p.parse_args()
    try:
        result=build(a.generation,a.out)if a.stage=='build'else run(a.generation,a.compiled,a.scenario,a.out)
    except (ValueError,KeyError)as e:
        result=dict(schema='spec-flow-stage-v1',stage=a.stage,status='rejected',classification='invalid_input_or_evidence',reason=str(e))
    except OSError as e:
        result=dict(schema='spec-flow-stage-v1',stage=a.stage,status='blocked',classification='environment',reason=str(e))
    except subprocess.TimeoutExpired:
        result=dict(schema='spec-flow-stage-v1',stage=a.stage,status='fail',classification='resource_limit',reason='Stage subprocess deadline exceeded')
    print(json.dumps(result));raise SystemExit(0 if result['status']=='pass'else 1)
