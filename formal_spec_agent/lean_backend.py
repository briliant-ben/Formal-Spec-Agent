"""Optional Lean expression contracts; proof data cannot edit approved statements."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

from protocol_lab.ir import load, model_files, infer, value_ok

HERE = Path(__file__).resolve().parent
VERSION = '4.35.0'
AXIOMS = {'propext', 'Quot.sound', 'Classical.choice'}
SCOPE = 'Selected pure event expression only; not EFSM transitions, C refinement, wire behavior, scheduler or whole-protocol correctness.'


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + '\n')


def inside(root, name):
    if type(name) is not str or Path(name).is_absolute():
        raise ValueError('Relative workspace input required')
    p = (root/name).resolve()
    if not p.is_relative_to(root) or not p.is_file():
        raise ValueError('Input missing or escapes workspace')
    return p


def number(n):
    if type(n) is not int:
        raise ValueError('Integer literal required')
    return '(' + str(n) + ')'


def literal(value, kind):
    if not value_ok(value, kind):
        raise ValueError('Invalid witness field')
    if kind == 'int': return number(value)
    if kind == 'bool': return 'true' if value else 'false'
    if kind == 'bytes': return '[' + ', '.join('⟨'+str(b)+', by decide⟩' for b in value) + ']'
    raise ValueError('Unsupported Lean field type')


def prepare(task_file, workspace, task_sha256, *, draft=False):
    root = Path(workspace).resolve(); task_file = Path(task_file).resolve()
    if not task_file.is_relative_to(root) or sha(task_file) != task_sha256:
        raise ValueError('Task outside workspace or digest mismatch')
    task = json.loads(task_file.read_text())
    if task.get('schema')=='fsa-lean-batch-task-v1':
        from .lean_batch import prepare as prepare_batch
        return prepare_batch(task_file,root,task_sha256,draft=draft)
    if task.get('schema')=='fsa-lean-machine-task-v1':
        from .lean_machine import prepare as prepare_machine
        return prepare_machine(task_file,root,task_sha256,draft=draft)
    if task.get('schema')=='fsa-lean-typed-expression-task-v1':
        from .lean_typed import prepare as prepare_typed
        return prepare_typed(task_file,root,task_sha256,draft=draft)
    if task.get('schema')=='fsa-lean-efsm-task-v1':
        from .lean_efsm import prepare as prepare_efsm
        return prepare_efsm(task_file,root,task_sha256,draft=draft)
    if task.get('schema')=='fsa-lean-state-task-v1':
        from .lean_state import prepare as prepare_state
        return prepare_state(task_file,root,task_sha256,draft=draft)
    if task.get('schema')=='fsa-lean-c-expression-task-v1':
        from .lean_c import prepare as prepare_c
        return prepare_c(task_file,root,task_sha256,draft=draft)
    keys = {'schema','id','model','model_sha256','sources','target','range','witnesses','lean_version','foundation_sha256','approved_sha256'}
    if set(task) != keys or task['schema'] != 'fsa-lean-expression-task-v1' or task['lean_version'] != VERSION:
        raise ValueError('Unsupported Lean task fields/version')
    if not re.fullmatch(r'[A-Za-z0-9_-]{1,80}', task['id']): raise ValueError('Invalid task identity')
    if sha(HERE/'lean/Foundation.lean') != task['foundation_sha256']:
        raise ValueError('Frozen Lean semantic definitions changed')
    model_file = inside(root, task['model'])
    chain=model_files(model_file)
    paths = [task_file, *chain]
    pinned_sources=set()
    if sha(model_file) != task['model_sha256']: raise ValueError('Model digest mismatch')
    if type(task['sources']) is not list or not task['sources']: raise ValueError('Pinned specification sources required')
    for s in task['sources']:
        if set(s) != {'path','sha256'}: raise ValueError('Invalid specification binding')
        p = inside(root, s['path'])
        if sha(p) != s['sha256']: raise ValueError('Specification digest mismatch')
        paths.append(p);pinned_sources.add(p)
    if not set(chain[1:])<=pinned_sources: raise ValueError('Every extended model base must be independently hash-pinned')
    if any(not p.is_relative_to(root) for p in paths): raise ValueError('Model base escapes workspace')
    m = load(model_file)
    if m['ir_version'] not in ('0.5','0.6') or m['semantics'] != 'flat-efsm-atomic-ordered-v1':
        raise ValueError('Lean unit requires atomic ordered IR0.5/0.6')
    target = task['target']
    if set(target) != {'rule','action'} or type(target['action']) is not int or target['action'] < 0:
        raise ValueError('Explicit rule/action expression target required')
    rules = [r for r in m['transitions'] if r['id'] == target['rule']]
    if len(rules) != 1: raise ValueError('Unknown target rule')
    r = rules[0]
    if target['action'] >= len(r['actions']): raise ValueError('Unknown action index')
    action = r['actions'][target['action']]
    if set(action) != {'set'}: raise ValueError('Only selected integer assignment expressions supported')
    e = action['set']['value']; event = r['event']; fields = m['events'][event]['fields']
    if infer(e, m, event) != 'int' or any(k not in ('int','bool','bytes') for k in fields.values()):
        raise ValueError('Unsupported expression/field type')
    if not fields: raise ValueError('Nonempty event context required by this Lean unit')
    kinds = {'int':'Int', 'bool':'Bool', 'bytes':'FormalSpecAgent.Bytes'}
    names = list(fields); binders = ' '.join('(f'+str(i)+' : '+kinds[k]+')' for i,k in enumerate(fields.values()))
    args = ' '.join('f'+str(i) for i in range(len(fields)))
    def lower(e):
        if type(e) is bool: return 'true' if e else 'false'
        if type(e) is int: return number(e)
        if type(e) is not dict: raise ValueError('Unsupported Lean expression literal')
        if set(e) == {'bytes'}: return '('+literal(e['bytes'],'bytes')+' : FormalSpecAgent.Bytes)'
        if set(e) == {'event'}: return 'f'+str(names.index(e['event']))
        if set(e) != {'op','args'}: raise ValueError('Lean unit supports pure event expressions only')
        a = [lower(x) for x in e['args']]; op = e['op']
        if op == 'bytes_at_or_zero': return '(FormalSpecAgent.byteAt '+a[0]+' '+a[1]+')'
        if op == 'bytes_slice': return '(FormalSpecAgent.byteSlice '+ ' '.join(a)+')'
        if op == 'bytes_len': return '(Int.ofNat '+a[0]+'.length)'
        if op == 'ite': return '(if '+a[0]+' then '+a[1]+' else '+a[2]+')'
        raise ValueError('Unsupported Lean operator: '+op)
    expression = lower(e)
    bounds = task['range']
    if set(bounds) != {'min','max'} or any(type(n) is not int for n in bounds.values()) or bounds['min'] > bounds['max']:
        raise ValueError('Invalid range contract')
    statements = {
        'byte_at_range':'∀ (xs : FormalSpecAgent.Bytes) (i : Int), 0 <= FormalSpecAgent.byteAt xs i ∧ FormalSpecAgent.byteAt xs i < 256',
        'negative_read':'∀ (xs : FormalSpecAgent.Bytes) (i : Int), i < 0 → FormalSpecAgent.byteAt xs i = 0',
        'slice_length':'∀ (xs : FormalSpecAgent.Bytes) (offset count : Int), (FormalSpecAgent.byteSlice xs offset count).length <= xs.length ∧ (FormalSpecAgent.byteSlice xs offset count).length <= count.toNat',
        'expression_range':'∀ '+binders+', '+number(bounds['min'])+' <= expression '+args+' ∧ expression '+args+' <= '+number(bounds['max']),
    }
    witnesses = task['witnesses']
    if type(witnesses) is not list or not 1 <= len(witnesses) <= 32: raise ValueError('Explicit positive witness contracts required')
    nonzero = False
    for w in witnesses:
        if set(w) != {'id','fields','expected'} or not re.fullmatch(r'[a-z][a-z0-9_]{0,50}',w['id']): raise ValueError('Invalid witness schema')
        name = 'witness_'+w['id']
        if name in statements or set(w['fields']) != set(fields) or type(w['expected']) is not int: raise ValueError('Invalid witness fields/identity')
        values = ' '.join('('+literal(w['fields'][n],k)+')' for n,k in fields.items())
        statements[name] = 'expression '+values+' = '+number(w['expected'])
        nonzero |= w['expected'] != 0
    if not nonzero: raise ValueError('At least one nonzero delivery witness required')
    source = 'import Foundation\n\nnamespace Approved\n\ndef expression '+binders+' : Int :=\n  '+expression+'\n\n'
    source += '\n\n'.join('def '+n+' : Prop :=\n  '+s for n,s in statements.items())+'\n\nend Approved\n'
    if not draft and hashlib.sha256(source.encode()).hexdigest() != task['approved_sha256']:
        raise ValueError('Generated statements differ from the approved frozen definitions')
    inputs = {'workspace/'+str(p.relative_to(root)):sha(p) for p in paths}
    inputs.update({'tool/'+str(p.relative_to(HERE)):sha(p) for p in [Path(__file__).resolve(),HERE/'lean/Foundation.lean',HERE/'lean/lean-toolchain']})
    inputs['ir_checker'] = sha(HERE.parent/'protocol_lab/ir.py')
    return source, list(statements), inputs


# A finite proof-data language, not arbitrary Lean source. Candidate data cannot
# add imports, declarations, axioms, commands, options, macros or executable IO.
# Terms are single-line, command-free applications; the trusted renderer owns all
# theorem headers and files. This is not an OS sandbox for an untrusted Lean binary.
NAME = re.compile(r'[A-Za-z_][A-Za-z0-9_.?]*\Z')
TERM = re.compile(r'[A-Za-z0-9_().,: +*/<>=?\-]+\Z')
FORBIDDEN = {'sorry','admit','axiom','unsafe','native_decide','run_tac','run_elab','elab','macro','syntax','initialize','set_option','import','namespace','section','end','def','theorem','example','instance','attribute','by','let','match','do'}


def term(s):
    if type(s) is not str or len(s) > 2000 or not TERM.fullmatch(s) or FORBIDDEN.intersection(re.findall(r'[A-Za-z_][A-Za-z0-9_]*',s)):
        raise ValueError('Unsupported proof term or forbidden declaration/escape')
    return s


def names(items):
    if type(items) is not list or not items or any(type(n) is not str or not NAME.fullmatch(n) for n in items): raise ValueError('Proof name list required')
    return [term(n) for n in items]


def proof_lines(steps, indent=2, depth=0):
    if depth > 20 or type(steps) is not list or not steps or len(steps) > 100: raise ValueError('Invalid proof data size/depth')
    rows=[]; pad=' '*indent
    for step in steps:
        if type(step) is not dict or len(step)!=1: raise ValueError('Single proof instruction required')
        k,v=next(iter(step.items()))
        if k in ('intro','unfold'):
            ns=names(v)
            if k=='intro' and any('.' in n for n in ns): raise ValueError('Local binder name required')
            rows.append(pad+k+' '+' '.join(ns))
        elif k in ('omega','rfl','decide','assumption'):
            if v is not True: raise ValueError('Proof instruction requires true')
            rows.append(pad+k)
        elif k in ('exact','apply'):
            rows.append(pad+k+' '+term(v))
        elif k in ('simp','simp_all','dsimp','simp_only'):
            if type(v) is not list: raise ValueError('Simp name list required')
            ns=names(v) if v else []
            rows.append(pad+('simp only'if k=='simp_only'else k)+(' ['+', '.join(ns)+']'if ns else''))
        elif k=='rewrite':
            rows.append(pad+'rw ['+', '.join(names(v))+']')
        elif k=='attempt':
            rows.append(pad+'try')
            rows.extend(proof_lines(v,indent+2,depth+1))
        elif k=='have':
            if type(v) is not dict or set(v)!={'name','term'} or not NAME.fullmatch(v['name']) or '.' in v['name']: raise ValueError('Invalid local lemma')
            rows.append(pad+'have '+term(v['name'])+' := '+term(v['term']))
        elif k in ('split','constructor'):
            if type(v) is not list or len(v)!=2: raise ValueError('Two explicit branches required')
            rows.append(pad+k)
            for branch in v:
                rows.append(pad+'·')
                rows.extend(proof_lines(branch,indent+2,depth+1))
        elif k=='unfold_at':
            if type(v)is not dict or set(v)!={'definitions','hypothesis'}or not NAME.fullmatch(v['hypothesis'])or '.'in v['hypothesis']:raise ValueError('Local hypothesis and unfold definitions required')
            rows.append(pad+'unfold '+' '.join(names(v['definitions']))+' at '+term(v['hypothesis']))
        elif k=='induction':
            if type(v)is not str or not NAME.fullmatch(v)or '.'in v:raise ValueError('Local induction binder required')
            rows.append(pad+'induction '+term(v))
        elif k=='all_goals':
            rows.append(pad+'all_goals')
            rows.extend(proof_lines(v,indent+2,depth+1))
        elif k=='cases':
            if type(v) is not dict or set(v)!={'name','branches'} or not NAME.fullmatch(v['name']) or type(v['branches']) is not list or len(v['branches'])!=2: raise ValueError('Two explicit cases required')
            rows.append(pad+'cases '+term(v['name']))
            for branch in v['branches']:
                rows.append(pad+'·'); rows.extend(proof_lines(branch,indent+2,depth+1))
        else: raise ValueError('Unsupported proof instruction: '+k)
    return rows


def unit_scope(inputs):
    if 'tool/lean/BatchMachine.lean'in inputs:
        from .lean_batch import SCOPE as batch_scope
        return batch_scope
    if 'tool/lean/TypedMachine.lean'in inputs:
        from .lean_machine import SCOPE as machine_scope
        return machine_scope
    if 'tool/lean/TypedIR.lean'in inputs:
        from .lean_typed import SCOPE as typed_scope
        return typed_scope
    if 'tool/lean/EfsmSubset.lean'in inputs:
        from .lean_efsm import SCOPE as efsm_scope
        return efsm_scope
    if 'tool/lean/StateSubset.lean'in inputs:
        from .lean_state import SCOPE as state_scope
        return state_scope
    if 'tool/lean/CSubset.lean'in inputs:
        from .lean_c import SCOPE as c_scope
        return c_scope
    return SCOPE


def contract_status(inputs):
    if 'tool/lean/BatchMachine.lean'in inputs:return 'checked_batch_contract'
    if 'tool/lean/TypedMachine.lean'in inputs:return 'checked_scheduled_microstep_contract'
    if 'tool/lean/TypedIR.lean'in inputs:return 'checked_typed_expression_contract'
    if 'tool/lean/EfsmSubset.lean'in inputs:return 'checked_efsm_contract'
    if 'tool/lean/StateSubset.lean'in inputs:return 'checked_state_contract'
    return 'checked_expression_contract'


def resources_for(inputs):
    return ['Foundation']+[n for n in ['CSubset','StateSubset','EfsmSubset','ValueOps','TypedIR','TypedMachine','StoreFacts','TimerRank','TimerMinimum','TimerEffects','TimerProgress','BatchMachine','BatchReplay','MachineObserve','BatchObserve']if 'tool/lean/'+n+'.lean'in inputs]


def proof_prefix(inputs):
    # Fixed declared capacity for typed buffer witnesses, not worker options.
    return 'import Approved\n\n'+('set_option maxRecDepth 16384\n\n'if 'tool/lean/TypedIR.lean'in inputs else'')+'namespace Proofs\n\n'


def resource_failure(returncode,stdout,stderr):
    if returncode is None:return True
    messages=stdout+'\n'+stderr
    return returncode==1 and bool(re.search(r'(?m)^(?:[^\n]*:\d+:\d+: )?error(?:\([^\n]*\))?: (?:Tactic `[^`]+` failed with a nested error:\n)?(?:maximum recursion depth has been reached|maximum number of heartbeats|\(deterministic\) timeout)',messages))


def semantic_audit_targets(inputs):
    if 'tool/lean/BatchMachine.lean'not in inputs:return []
    return ['FormalSpecAgent.TimerMinimum.next_info',
            'FormalSpecAgent.TimerEffects.work_summary',
            'FormalSpecAgent.TimerProgress.step_progress',
            *['FormalSpecAgent.BatchMachine.'+n for n in ['advanceAux','advance','tick','dispatch','rollback']],
            *(['FormalSpecAgent.BatchReplay.'+n for n in ['sound','advance_result','tick_failure','tick_success','dispatch_timer_failure','dispatch_after_timers','prefix_failure_rolls_back']]if 'tool/lean/BatchReplay.lean'in inputs else [])]


def read_axioms(text,name):
    prefix="'"+name+"' "
    if prefix+'does not depend on any axioms'in text:return []
    match=re.search(re.escape(prefix)+r'depends on axioms: \[([^\]]*)\]',text)
    if not match:raise ValueError('Missing kernel axiom audit for '+name)
    found=[x.strip()for x in match[1].split(',')if x.strip()]
    if set(found)-AXIOMS:raise ValueError('Unapproved semantic/proof axiom')
    return found


def check(task_file, workspace, out, proofs_file, task_sha256, lean='lean'):
    root=Path(workspace).resolve(); out=Path(out).resolve(); proofs_file=Path(proofs_file).resolve()
    if out.exists() or out.is_relative_to(root) or out.is_relative_to(HERE.parent): raise ValueError('Fresh output outside workspace and framework required')
    approved,goals,inputs=prepare(task_file,root,task_sha256)
    proofs_bytes=proofs_file.read_bytes()
    if len(proofs_bytes)>100000: raise ValueError('Proof data too large')
    proofs=json.loads(proofs_bytes)
    if type(proofs) is not dict or set(proofs)!=set(goals): raise ValueError('Every frozen obligation requires exactly one proof')
    candidate=proof_prefix(inputs)
    for n in goals:
        candidate+='theorem '+n+' : Approved.'+n+' := by\n'+'\n'.join(proof_lines(proofs[n]))+'\n\n'
    candidate+='end Proofs\n'
    audit='import Proofs\n\n'
    for n in goals:
        audit+='example : Approved.'+n+' := Proofs.'+n+'\n#print axioms Proofs.'+n+'\n'
    for name in semantic_audit_targets(inputs):audit+='#print axioms '+name+'\n'
    out.mkdir(parents=True)
    resources=resources_for(inputs)
    for module in resources:(out/(module+'.lean')).write_bytes((HERE/('lean/'+module+'.lean')).read_bytes())
    for n,s in [('Approved.lean',approved),('Proofs.lean',candidate),('Audit.lean',audit)]: (out/n).write_text(s)
    (out/'proofs.json').write_bytes(proofs_bytes)
    source_hashes={p.name:sha(p)for p in out.glob('*.lean')}
    for name in source_hashes: (out/name).chmod(0o444)
    result=dict(schema='fsa-lean-expression-result-v1',status='incomplete',scope=unit_scope(inputs),task_sha256=task_sha256,proofs_sha256=hashlib.sha256(proofs_bytes).hexdigest(),inputs=inputs,sources=source_hashes,goals=goals,allowed_axioms=sorted(AXIOMS),compiler_correctness_proved=False,protocol_correctness_proved=False)
    tool=shutil.which(str(lean))
    if not tool:
        result.update(status='blocked',classification='environment',reason='Pinned Lean checker unavailable')
        write(out/'result.json',result); return result
    tool=str(Path(tool).resolve())
    version=subprocess.check_output([tool,'--version'],text=True,timeout=15)
    if not re.search(r'\bversion '+re.escape(VERSION)+r'(?:,|\))',version): raise ValueError('Pinned Lean version required')
    result.update(lean_version=version.strip(),lean_binary_sha256=sha(Path(tool).resolve()),commands=[])
    env=dict(PATH=os.defpath,LEAN_PATH=str(out),LANG='C.UTF-8')
    for n in [*resources,'Approved','Proofs','Audit']:
        cmd=[tool,'-o',n+'.olean',n+'.lean']
        try:
            p=subprocess.run(cmd,cwd=out,env=env,capture_output=True,text=True,timeout=60)
            stdout,stderr,rc=p.stdout,p.stderr,p.returncode
        except subprocess.TimeoutExpired as e:
            stdout=(e.stdout or b'').decode()if isinstance(e.stdout,bytes)else(e.stdout or'')
            stderr='Lean wall-clock timeout';rc=None
        (out/(n+'.stdout')).write_text(stdout);(out/(n+'.stderr')).write_text(stderr)
        result['commands'].append(dict(module=n,returncode=rc,stdout_sha256=sha(out/(n+'.stdout')),stderr_sha256=sha(out/(n+'.stderr'))))
        if rc!=0:
            result.update(status='fail',classification='resource_unknown'if resource_failure(rc,stdout,stderr)else'tool_execution_failure'if rc<0 else'proof_failure',failed_module=n)
            break
    else:
        axioms={};text=(out/'Audit.stdout').read_text()
        for n in goals:
            prefix="'Proofs."+n+"' "
            if prefix+'does not depend on any axioms' in text: found=[]
            else:
                match=re.search(re.escape(prefix)+r'depends on axioms: \[([^\]]*)\]',text)
                if not match: raise ValueError('Missing kernel axiom audit for '+n)
                found=[x.strip()for x in match[1].split(',')if x.strip()]
            if set(found)-AXIOMS: raise ValueError('Unapproved proof axioms')
            axioms[n]=found
        semantic_axioms={name:read_axioms(text,name)for name in semantic_audit_targets(inputs)}
        result['semantic_axioms']=semantic_axioms
        kind=contract_status(inputs)
        result.update(status=kind,axioms=axioms,c_expression_model_refinement_checked=('tool/lean/CSubset.lean'in inputs),state_action_contract_checked=kind=='checked_state_contract',efsm_contract_checked=kind=='checked_efsm_contract',typed_expression_contract_checked=kind=='checked_typed_expression_contract',scheduled_microstep_contract_checked=kind=='checked_scheduled_microstep_contract',batch_contract_checked=kind=='checked_batch_contract')
    # Frozen input and generated-file identity is rechecked after the actual tool.
    try:
        stable=prepare(task_file,root,task_sha256)[2]==inputs and proofs_file.read_bytes()==proofs_bytes and all(sha(out/n)==h for n,h in source_hashes.items())
    except (ValueError,OSError):
        stable=False
    if not stable:
        result.update(status='invalidated_inputs',classification='evidence_changed',c_expression_model_refinement_checked=False,state_action_contract_checked=False,efsm_contract_checked=False,typed_expression_contract_checked=False,scheduled_microstep_contract_checked=False,batch_contract_checked=False)
    result['outputs']={p.name:sha(p)for p in out.iterdir()if p.is_file()}
    write(out/'result.json',result);return result


def plan_main(argv=None):
    p=argparse.ArgumentParser(description='Render an unapproved Lean statement draft; no proof or acceptance')
    p.add_argument('task',type=Path);p.add_argument('--workspace',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--task-sha256',required=True)
    a=p.parse_args(argv)
    try:
        root=Path(a.workspace).resolve();out=Path(a.out).resolve()
        if out.exists()or out.is_relative_to(root)or out.is_relative_to(HERE.parent):raise ValueError('Fresh external output required')
        source,goals,inputs=prepare(a.task,root,a.task_sha256,draft=True)
        out.mkdir(parents=True);(out/'Approved.lean').write_text(source)
        result=dict(status='draft_requires_independent_approval',approved_sha256=sha(out/'Approved.lean'),goals=goals,inputs=inputs,proof_checked=False,scope=unit_scope(inputs))
        write(out/'plan.json',result);print(json.dumps(result));return 0
    except (ValueError,OSError)as e:
        print(json.dumps(dict(status='rejected',reason=str(e))),file=sys.stderr);return 2


def inspect_certificate(bundle, task_file, workspace, task_sha256, *, require_pass=True):
    """Retained integrity only. Reconstruct trusted source, never execute archives.

    Actual historical kernel execution/authenticity needs a trusted provenance;
    call verify for fresh kernel checking. This helper never supplies a new proof.
    """
    bundle=Path(bundle).resolve()
    result=json.loads((bundle/'result.json').read_text())
    completed=result.get('status')in ('checked_expression_contract','checked_state_contract','checked_efsm_contract','checked_typed_expression_contract','checked_scheduled_microstep_contract','checked_batch_contract')
    partial=not require_pass and result.get('status')=='fail'and result.get('classification')=='resource_unknown'
    if result.get('schema')!='fsa-lean-expression-result-v1' or not (completed or partial):
        raise ValueError('Only completed scoped Lean certificates can be rechecked')
    expected=result['outputs']
    if any(p.is_symlink()for p in bundle.iterdir()): raise ValueError('Retained evidence must not contain symlinks')
    actual={p.name for p in bundle.iterdir()if p.is_file()and p.name!='result.json'}
    if set(expected)!=actual or any(sha(bundle/n)!=h for n,h in expected.items()):
        raise ValueError('Retained evidence changed')
    approved,goals,inputs=prepare(task_file,workspace,task_sha256)
    if result['task_sha256']!=task_sha256 or result['inputs']!=inputs:
        raise ValueError('Task/checker epoch differs from retained certificate')
    expected_status=contract_status(inputs)
    if completed and result['status']!=expected_status or result.get('state_action_contract_checked',False)!=(completed and expected_status=='checked_state_contract'):
        raise ValueError('Retained certificate claim differs from its task')
    if result.get('efsm_contract_checked',False)!=(completed and expected_status=='checked_efsm_contract'):
        raise ValueError('Retained EFSM claim differs from its task')
    if result.get('batch_contract_checked',False)!=(completed and expected_status=='checked_batch_contract'):
        raise ValueError('Retained batch claim differs from its task')
    if result.get('scheduled_microstep_contract_checked',False)!=(completed and expected_status=='checked_scheduled_microstep_contract'):
        raise ValueError('Retained scheduled-microstep claim differs from its task')
    if result.get('typed_expression_contract_checked',False)!=(completed and expected_status=='checked_typed_expression_contract'):
        raise ValueError('Retained typed-expression claim differs from its task')
    if result.get('c_expression_model_refinement_checked',False)!=(completed and 'tool/lean/CSubset.lean'in result['inputs']) or result.get('scope')!=unit_scope(result['inputs']) or result.get('compiler_correctness_proved') is not False or result.get('protocol_correctness_proved') is not False:
        raise ValueError('Retained certificate scope/claim differs from its task')
    if sha(bundle/'proofs.json')!=result['proofs_sha256']: raise ValueError('Retained proof data changed')
    proofs=json.loads((bundle/'proofs.json').read_text())
    if type(proofs)is not dict or set(proofs)!=set(goals)or result['goals']!=goals:raise ValueError('Retained proof/goal coverage differs')
    candidate=proof_prefix(inputs)
    audit='import Proofs\n\n'
    for n in goals:
        candidate+='theorem '+n+' : Approved.'+n+' := by\n'+'\n'.join(proof_lines(proofs[n]))+'\n\n'
        audit+='example : Approved.'+n+' := Proofs.'+n+'\n#print axioms Proofs.'+n+'\n'
    candidate+='end Proofs\n'
    for name in semantic_audit_targets(inputs):audit+='#print axioms '+name+'\n'
    sources={n+'.lean':(HERE/('lean/'+n+'.lean')).read_text()for n in resources_for(inputs)}
    sources.update({'Approved.lean':approved,'Proofs.lean':candidate,'Audit.lean':audit})
    expected_hashes={n:hashlib.sha256(s.encode()).hexdigest()for n,s in sources.items()}
    if result['sources']!=expected_hashes or any((bundle/n).read_text()!=s for n,s in sources.items()):raise ValueError('Retained sources differ from trusted reconstruction')
    expected_modules=[*resources_for(inputs),'Approved','Proofs','Audit']
    if partial:
        commands=result.get('commands',[])
        if result.get('axioms')or not commands or [c.get('module')for c in commands]!=expected_modules[:len(commands)]or any(c.get('returncode')!=0 for c in commands[:-1]):raise ValueError('Retained unresolved checker prefix differs')
        if any(c.get('stdout_sha256')!=sha(bundle/(c['module']+'.stdout'))or c.get('stderr_sha256')!=sha(bundle/(c['module']+'.stderr'))for c in commands):raise ValueError('Retained unresolved checker logs differ')
        last=commands[-1]
        if not resource_failure(last['returncode'],(bundle/(last['module']+'.stdout')).read_text(),(bundle/(last['module']+'.stderr')).read_text()):raise ValueError('Retained unresolved checker reason differs')
        return result
    if result.get('allowed_axioms')!=sorted(AXIOMS)or set(result.get('axioms',{}))!=set(goals):raise ValueError('Retained axiom audit coverage differs')
    text=(bundle/'Audit.stdout').read_text()
    targets=semantic_audit_targets(inputs)
    if result.get('semantic_axioms',{})!={name:read_axioms(text,name)for name in targets}:raise ValueError('Retained semantic axiom claim differs')
    for n in goals:
        prefix="'Proofs."+n+"' "
        if prefix+'does not depend on any axioms'in text:found=[]
        else:
            match=re.search(re.escape(prefix)+r'depends on axioms: \[([^\]]*)\]',text)
            if not match:raise ValueError('Missing retained axiom audit')
            found=[x.strip()for x in match[1].split(',')if x.strip()]
        if set(found)-AXIOMS or found!=result['axioms'][n]:raise ValueError('Retained axiom audit claim differs')
    if [c.get('module')for c in result.get('commands',[])]!=expected_modules or any(c.get('returncode')!=0 or c.get('stdout_sha256')!=sha(bundle/(c['module']+'.stdout'))or c.get('stderr_sha256')!=sha(bundle/(c['module']+'.stderr'))for c in result['commands']):raise ValueError('Retained successful checker commands differ')
    return result


def verify(bundle, task_file, workspace, out, task_sha256, lean='lean'):
    """Rebuild approved statements with the trusted checker; never run archived Lean."""
    bundle=Path(bundle).resolve()
    result=inspect_certificate(bundle,task_file,workspace,task_sha256)
    fresh=check(task_file,workspace,out,bundle/'proofs.json',task_sha256,lean)
    if fresh['sources']!=result['sources'] or fresh['goals']!=result['goals']:
        raise ValueError('Fresh statement/proof rendering differs')
    return fresh


def verify_main(argv=None):
    p=argparse.ArgumentParser(description='Recheck Lean proof data using freshly regenerated approved source, never archived code')
    p.add_argument('bundle',type=Path);p.add_argument('--task',type=Path,required=True);p.add_argument('--workspace',type=Path,required=True)
    p.add_argument('--out',type=Path,required=True);p.add_argument('--task-sha256',required=True);p.add_argument('--lean',default='lean')
    a=p.parse_args(argv)
    try:
        r=verify(a.bundle,a.task,a.workspace,a.out,a.task_sha256,a.lean);print(json.dumps(r));return 0 if r['status']in ('checked_expression_contract','checked_state_contract','checked_efsm_contract','checked_typed_expression_contract','checked_scheduled_microstep_contract','checked_batch_contract')else 1
    except (ValueError,OSError,subprocess.SubprocessError)as e:
        print(json.dumps(dict(status='rejected',reason=str(e))),file=sys.stderr);return 2


def main(argv=None):
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('task',type=Path);p.add_argument('--workspace',type=Path,required=True);p.add_argument('--out',type=Path,required=True)
    p.add_argument('--proofs',type=Path,required=True);p.add_argument('--task-sha256',required=True);p.add_argument('--lean',default='lean')
    a=p.parse_args(argv)
    try:
        r=check(a.task,a.workspace,a.out,a.proofs,a.task_sha256,a.lean);print(json.dumps(r));return 0 if r['status']in ('checked_expression_contract','checked_state_contract','checked_efsm_contract','checked_typed_expression_contract','checked_scheduled_microstep_contract','checked_batch_contract')else 1
    except (ValueError,OSError,subprocess.SubprocessError)as e:
        print(json.dumps(dict(status='rejected',reason=str(e))),file=sys.stderr);return 2
