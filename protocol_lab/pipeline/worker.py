"""Fixed stage worker. Task data never supplies Python or shell commands."""
import argparse
import copy
import json
from pathlib import Path
import subprocess
import traceback
from ..ir import load,Machine,ModelError,Uncovered,Conflict
from ..codegen import generate as generate_native,Unsupported,sha
from ..codegen.execute import build,commands
from .task import read,write,resolve
from .testgen import generate as generate_tests,classification

KEYS=('transition','requirements','time_ms','event','after','emitted')
SHAPES={'ready':{'status','snapshot'},'ok':{'status','snapshot'},
        'error':{'status','failure','snapshot'},'transition':{'status',*KEYS}}


def result(status='pass',classification=None,data=None):return dict(status=status,classification=classification,data=data or {})
def prior(job,name):return read(job/'stages'/name/'result.json')['data']
def cases(job):return prior(job,'tests')['cases']
def apply(machine,step):
    if step.get('tick'):machine.tick(step['at_ms'])
    else:machine.dispatch(step['event'],step.get('fields',{}),step['at_ms'])


def reference_case(model,case):
    machine=Machine(model,case.get('initial',{}));initial=machine.snapshot();operations=[];error=None
    for step in case['steps']:
        try:apply(machine,step)
        except ModelError as e:error=dict(classification=classification(e),message=str(e));break
        operations.append(machine.snapshot())
    if error is None and 'settle_ms'in case:
        try:machine.tick(case['settle_ms']);operations.append(machine.snapshot())
        except ModelError as e:error=dict(classification=classification(e),message=str(e))
    return dict(initial=initial,operations=operations,error=error,
                trace=[{k:r[k]for k in KEYS}for r in machine.trace],final=machine.snapshot())


def native_class(name):
    if name=='uncovered_event':return 'model_gap'
    if name=='rule_conflict':return 'rule_conflict'
    if name.startswith('invariant:'):return 'invariant_failure'
    if name in ('integer_overflow','byte_capacity','output_capacity','input_capacity','timer_step_capacity'):return 'backend_domain_exceeded'
    return 'invalid_input_or_model'


def compare_case(expected,observed,native_returncode,negative):
    if not observed or observed[0].get('status')!='ready':return result('fail','invalid_observation')
    for r in observed:
        if r.get('status')not in SHAPES or set(r)!=SHAPES[r['status']]:return result('fail','invalid_observation')
    if sum(r['status']=='ready'for r in observed)!=1:return result('fail','invalid_observation')
    actual=[{k:r[k]for k in KEYS}for r in observed if r['status']=='transition']
    operations=[r['snapshot']for r in observed if r['status']=='ok']
    errors=[r for r in observed if r['status']=='error'];differences=[]
    if observed[0]['snapshot']!=expected['initial']:differences.append('initial_snapshot')
    if actual!=expected['trace']:differences.append('transition_trace')
    if operations!=expected['operations']:differences.append('operation_snapshots')
    if observed[-1].get('snapshot')!=expected['final']:differences.append('final_snapshot')
    if negative:
        if not expected['error']or len(errors)!=1 or native_returncode!=1 or observed[-1]['status']!='error':differences.append('expected_atomic_rejection')
        elif native_class(errors[0]['failure'])!=expected['error']['classification']:differences.append('rejection_classification')
    elif expected['error']or errors or native_returncode!=0:differences.append('unexpected_rejection')
    verdict='backend_domain_exceeded'if any(native_class(e['failure'])=='backend_domain_exceeded'for e in errors)else'implementation_difference'
    return result('fail'if differences else'pass',verdict if differences else None,
                  dict(differences=differences,transitions_compared=len(expected['trace']),
                       negative_case=negative,expected=expected,observed=observed,
                       scope='fixed-input IR/reference/native correspondence; not specification correctness'))


def stage(name,t,workspace,job,out):
    model_file=resolve(workspace,t['model'])
    if name=='sources':
        rows=[dict(id=s['id'],version=s['version'],path=s['path'],expected=s['sha256'],observed=sha(resolve(workspace,s['path'])))for s in t['sources']]
        return result('pass'if all(r['expected']==r['observed']for r in rows)else'fail',
                      None if all(r['expected']==r['observed']for r in rows)else'source_integrity',dict(sources=rows))
    model=load(model_file)
    if name=='ir':
        from ..symbolic import model_hash
        return result(data=dict(model_semantic_sha256=model_hash(model),model_scope=model['scope'],
                                rules=len(model['transitions']),invariants=len(model['invariants'])))
    if name=='formal':
        if t['schema']=='spec-flow-task-v5':
            from ..initial_step import check, PASS, UNRESOLVED
            r=check(model,out/'queries',solver_timeout_ms=t['formal'].get('solver_timeout_ms',10000))
            status='pass' if r['status']==PASS else 'unknown' if r['status']==UNRESOLVED else 'fail'
            return result(status,None if status=='pass' else r['status'],r)
        if t['schema']=='spec-flow-task-v4':
            from ..sequence_induction import prove
            r=prove(model,out/'queries',solver_timeout_ms=t['formal'].get('solver_timeout_ms',10000))
            good='inductive_invariants_pass'
        else:
            from ..symbolic import check
            r=check(model,t['formal']['depth'],t['formal']['symbolic_initials'],out/'queries',solver_timeout_ms=t['formal'].get('solver_timeout_ms',10000),solver_preprocess=t['formal'].get('solver_preprocess','none'))
            good='bounded_pass'
        status='pass'if r['status']==good else'unknown'if r['status']in ('unknown','vacuous')else'fail'
        kind=None if status=='pass'else r['status']
        return result(status,kind,r)
    if name=='tests':
        r=generate_tests(model,read(resolve(workspace,t['exploration'])),out/'generated',t['limits']['max_prefixes'],t['limits']['max_cases'])
        rows=[]
        for p in r['positives']:
            rows.append(dict(key='case-'+str(len(rows)).zfill(4),path=str((out/'generated'/p['file']).relative_to(job)),origin='model_generated',negative=False,covers=p['covers']))
        seed_dir=out/'seeds';seed_dir.mkdir()
        for name in t['seeds']:
            p=seed_dir/('seed-'+str(len(rows))+'.json');write(p,read(resolve(workspace,name)))
            rows.append(dict(key='case-'+str(len(rows)).zfill(4),path=str(p.relative_to(job)),origin='declared_seed',negative=False))
        negative_dir=out/'negative';negative_dir.mkdir()
        for n in read(out/'generated/negative.json'):
            p=negative_dir/('case-'+str(len(rows))+'.json');write(p,n)
            rows.append(dict(key='case-'+str(len(rows)).zfill(4),path=str(p.relative_to(job)),origin='model_generated_rejection',negative=True))
        r['cases']=rows
        status='fail'if r['status']=='fail'else'unknown'if r['uncovered_rules']else'pass'
        return result(status,r['classification']or('coverage_gap'if status=='unknown'else None),r)
    if name=='reference':
        rows=[]
        for c in cases(job):
            case=read(job/c['path'])
            if not c['negative']:
                # Reuse the existing, independently authored scenario0.2 gate.
                # In particular, never reduce expect_trace to final-state checks.
                from ..flow import run_scenario,TraceContractMismatch
                try:
                    snapshots = []
                    machine = run_scenario(model,case,snapshots=snapshots)
                    r = {
                        'initial': snapshots[0],
                        'operations': snapshots[1:],
                        'error': None,
                        'trace': [{k: row[k] for k in KEYS} for row in machine.trace],
                        'final': machine.snapshot()
                    }
                except TraceContractMismatch as e:
                    return result('fail','scenario_contract',dict(scenario=e.scenario,at_ms=e.at_ms,expected=e.expected,observed=e.observed))
            else:
                r=reference_case(model,case)
            if c['negative']:
                if not r['error']or r['error']['classification']!=case['expected_rejection']:return result('fail','reference_rejection_mismatch')
            elif r['error']:return result('fail',r['error']['classification'],r)
            if not c['negative']:
                e=case['expect']
                if r['final']['state']!=e['state']or r['final']['timers']!=e['timers']or any(r['final']['variables'][k]!=v for k,v in e.get('variables',{}).items()):return result('fail','scenario_contract')
            p=out/(c['key']+'.json');write(p,r);rows.append(dict(key=c['key'],path=str(p.relative_to(job)),negative=c['negative'],
                             trace_contract_steps_checked=0 if c['negative']else sum('expect_trace'in step for step in case['steps'])))
        return result('pass'if rows else'unknown',None if rows else'no_reference_cases',dict(cases=rows,trace_contract_steps_checked=sum(r['trace_contract_steps_checked']for r in rows)))
    if name=='generate':
        data=generate_native(model_file,out/'generation')
        if 'wire'in t:data['wire_generation']=generate_native(model_file,out/'wire-generation',resolve(workspace,t['wire']['binding']))
        return result(data=data)
    if name=='build':
        r=build(job/'stages/generate/generation',out/'build')
        if 'wire'in t and r['status']=='pass':
            w=build(job/'stages/generate/wire-generation',out/'wire-build');r['wire_compile']=w
            if w['status']!='pass':return result(w['status'],w['classification'],r)
        return result(r['status'],r['classification'],r)
    if name=='execute':
        compiler=prior(job,'build');binary=job/'stages/build/build/protocol-native'
        if sha(binary)!=compiler['executable_sha256']:raise ValueError('Built executable changed')
        rows=[]
        for c in cases(job):
            folder=out/c['key'];folder.mkdir();case=read(job/c['path']);data=commands(model,case)
            (folder/'input.txt').write_text(data)
            p=subprocess.run([str(binary)],input=data,text=True,capture_output=True,timeout=30)
            (folder/'stdout').write_text(p.stdout);(folder/'stderr').write_text(p.stderr)
            rows.append(dict(key=c['key'],returncode=p.returncode,stdout=str((folder/'stdout').relative_to(job)),
                             stderr=str((folder/'stderr').relative_to(job)),negative=c['negative']))
        if sha(binary)!=compiler['executable_sha256']:raise ValueError('Executable changed during observation')
        wire_rows=[]
        if 'wire'in t:
            from ..codegen.wire_execute import run as run_wire
            for i,scenario in enumerate(t['wire']['scenarios']):
                folder=out/('wire-'+str(i).zfill(3))
                w=run_wire(job/'stages/generate/wire-generation',job/'stages/build/wire-build',resolve(workspace,scenario),folder)
                wire_rows.append(dict(scenario=scenario,status=w['status'],path=str((folder/'execution.json').relative_to(job)),native_egress_packets=w['native_egress_packets']))
        return result(data=dict(cases=rows,wire_cases=wire_rows,observation_origin='generated_native_execution',
                                executable_sha256=compiler['executable_sha256'],reference_values_supplied=False,
                                linux_network_evidence=False,pcap_evidence=False))
    if name=='compare':
        if not cases(job):return result('unknown','no_native_cases')
        refs={r['key']:r for r in prior(job,'reference')['cases']};rows=[]
        for r in prior(job,'execute')['cases']:
            try:observed=[json.loads(x)for x in (job/r['stdout']).read_text().splitlines()]
            except ValueError:return result('fail','invalid_observation')
            comparison=compare_case(read(job/refs[r['key']]['path']),observed,r['returncode'],r['negative'])
            if (job/r['stderr']).read_text():comparison=result('fail','native_stderr',comparison['data'])
            p=out/(r['key']+'.json');write(p,comparison)
            rows.append(dict(key=r['key'],status=comparison['status'],classification=comparison['classification'],path=str(p.relative_to(job))))
        wire_rows=prior(job,'execute').get('wire_cases',[])
        for w in wire_rows:
            observed=read(job/w['path'])
            if observed['status']!=w['status']or observed['observation_kind']!='generated_native_ipv4_virtual_link'or observed['linux_tcp_network_evidence']or observed['physical_network_evidence']:raise ValueError('Wire observation binding/scope differs')
        failures=[r for r in rows+wire_rows if r['status']!='pass']
        return result('fail'if failures else'pass',failures[0].get('classification','wire_implementation_difference')if failures else None,dict(cases=rows,wire_cases=wire_rows))
    if name=='traceability':
        sources={s['id']:s for s in t['sources']};bindings=t['requirement_bindings']
        if set(bindings)!=set(model['requirements']):raise ValueError('Incomplete requirement binding coverage')
        for key,req in model['requirements'].items():
            b=bindings[key];source=sources[b['source']]
            if b['reference']!=req['source']or req['source'].split('#')[0]not in source['uri_aliases']:raise ValueError('Requirement/source reference differs')
        rows=[dict(rule=r['id'],requirements=[dict(id=k,**bindings[k],interpretation=model['requirements'][k]['interpretation'],
                   source_sha256=sources[bindings[k]['source']]['sha256'])for k in r['requirements']])for r in model['transitions']]
        write(out/'rules.json',rows)
        return result(data=dict(rules=rows,source_to_ir_binding='structural_interpretation_record',
                                english_to_ir_correctness_proved=False))
    raise ValueError('Unknown fixed stage')


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('name',choices=('sources','ir','formal','tests','reference','generate','build','execute','compare','traceability'));p.add_argument('--job',type=Path,required=True)
    a=p.parse_args();job=a.job.resolve();config=read(job/'request.json');out=job/'stages'/a.name;out.mkdir(parents=True,exist_ok=False)
    try:r=stage(a.name,config['task'],Path(config.get('execution_workspace',config['workspace'])),job,out)
    except Unsupported as e:r=result('rejected','unsupported_semantics',dict(reason=str(e)))
    except ModelError as e:
        missing='Z3 is missing'in str(e)
        r=result('blocked'if missing else'fail','environment'if missing else classification(e),dict(reason=str(e)))
    except (ImportError,OSError)as e:r=result('blocked','environment',dict(reason=str(e)))
    except subprocess.TimeoutExpired:r=result('fail','resource_limit',dict(reason='Stage child deadline exceeded'))
    except (ValueError,KeyError,TypeError)as e:r=result('rejected','invalid_input_or_evidence',dict(reason=str(e)))
    except Exception as e:
        traceback.print_exc();r=result('fail','tool_error',dict(reason=str(e)))
    r.update(schema='spec-flow-stage-v1',stage=a.name);write(out/'result.json',r);print(json.dumps(r))
    return 0

if __name__=='__main__':raise SystemExit(main())
