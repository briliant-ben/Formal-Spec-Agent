"""Full Seq(BV8) invariant induction, distinct from bounded path checking.

No length projection, concrete-input substitution, reference callbacks or assumed
poststates. Reports concern declared invariants on defined atomic-v1 transitions,
not wire contents, event coverage, compiler correctness or the whole protocol.
"""
import hashlib
import itertools
import json
from pathlib import Path
from .ir import require,validate
from .symbolic import Encoding,model_hash

SCHEMA='full-sequence-invariant-induction-v1'


def digest(raw):return hashlib.sha256(raw).hexdigest()

def admitted(model):
    validate(model)
    require(model['ir_version']in ('0.4','0.5')and model['semantics']=='flat-efsm-atomic-ordered-v1','Sequence induction supports only IR0.4/0.5 atomic-v1')
    require(not model['scope']['terminal_states'],'Sequence induction does not support terminal-state contracts')
    require(bool(model['invariants']),'Sequence induction requires declared invariants')
    require(all('target_cases'not in r for r in model['transitions']),'Sequence induction requires fixed rule targets')
    def observe(node):
        if isinstance(node,dict):
            require('clock_ms'not in node and 'event'not in node,'Time/event-dependent invariant unsupported')
            for value in node.values():observe(value)
        elif isinstance(node,list):
            for value in node:observe(value)
    for inv in model['invariants']:observe(inv['assert'])


def groups(model):
    result=[]
    for state,event in sorted({(r['from'],r['event'])for r in model['transitions']}):
        ids=[i for i,r in enumerate(model['transitions'])if (r['from'],r['event'])==(state,event)]
        if len(ids)>1:result.append((state,event,ids))
    return result


def prove(model,out=None,solver_timeout_ms=10000):
    admitted(model);require(type(solver_timeout_ms)is int and 100<=solver_timeout_ms<=60000,'Invalid solver time budget')
    if out is not None:
        out=Path(out);require(not out.exists()or not any(out.iterdir()),'Fresh induction output directory required');out.mkdir(parents=True,exist_ok=True)
    files={}
    def record(enc,name):
        enc.solver.set(timeout=solver_timeout_ms);text=enc.solver.to_smt2();files[name]=text
        # Persist the exact query before solving so interruption keeps evidence.
        if out is not None:(out/name).write_text(text)
        answer=str(enc.solve());row=dict(file=name,query=answer,smt2_sha256=digest(text.encode()))
        if answer=='unknown':row['reason']=enc.reason_unknown()
        if answer=='sat'and not name.startswith(('enabled-','initial-enabled')):row['counterexample_model_sexpr']=enc.solver.model().sexpr()
        return row
    def fresh(enc,terms,fixes=()):
        z=enc.z;enc.solver=z.Solver();enc.solver.add(*[z.simplify(z.substitute(t,*fixes))if fixes else z.simplify(t)for t in terms])
    initial=Encoding(model,1,[]);z=initial.z;initial_terms=list(initial.solver.assertions())
    initial_bad=z.Not(z.And(*[initial.expr(i['assert'],initial.frames[0])for i in model['invariants']]))
    initial_fixes=[(z.Int('choice_0'),z.IntVal(-1))]
    fresh(initial,initial_terms+[initial_bad],initial_fixes);initial_query=record(initial,'initial.smt2')
    fresh(initial,initial_terms,initial_fixes);initial_enabled=record(initial,'initial-enabled.smt2')
    preservation=[]
    for index,rule in enumerate(model['transitions']):
        enc=Encoding(model,1,tuple(model['variables']),arbitrary_state=True,fixed_choices=[index]);old,new=enc.frames
        pre=[enc.expr(i['assert'],old)for i in model['invariants']]
        base=list(enc.solver.assertions())+pre
        post=[enc.expr(i['assert'],new)for i in model['invariants']]
        post+=[z.Implies(new['active'][n],new['due'][n]>=new['now'])for n in model['timers']]
        fixes=[(z.Int('choice_0'),z.IntVal(index)),(old['state'],z.IntVal(model['states'].index(rule['from']))),(new['state'],z.IntVal(model['states'].index(rule['to'])))]
        bad=z.Or(z.Not(z.And(*post)),*enc.action_faults)
        fresh(enc,base+[bad],fixes);obligation=record(enc,'preserve-'+str(index).zfill(4)+'.smt2')
        fresh(enc,base,fixes);enabled=record(enc,'enabled-'+str(index).zfill(4)+'.smt2')
        preservation.append(dict(rule=rule['id'],source=rule['from'],target=rule['to'],obligation=obligation,nonvacuity=enabled))
    overlap=[]
    for group,(state,event,indices)in enumerate(groups(model)):
        enc=Encoding(model,1,tuple(model['variables']),arbitrary_state=True);old=enc.frames[0]
        base=list(enc.solver.assertions())+[enc.expr(i['assert'],old)for i in model['invariants']]
        pairs=[z.And(enc.enabled[0][a][1],enc.enabled[0][b][1])for a,b in itertools.combinations(indices,2)]
        fresh(enc,base+[z.Or(*pairs)],[(old['state'],z.IntVal(model['states'].index(state)))])
        row=record(enc,'overlap-'+str(group).zfill(4)+'.smt2');overlap.append(dict(state=state,event=event,rules=[model['transitions'][i]['id']for i in indices],obligation=row))
    negative=[initial_query]+[r['obligation']for r in preservation+overlap]
    positive=[initial_enabled]+[r['nonvacuity']for r in preservation]
    if any(r['query']=='sat'for r in negative):status='inductive_obligation_failure'
    elif any(r['query']=='unknown'for r in negative+positive):status='unknown'
    elif any(r['query']!='sat'for r in positive):status='vacuous'
    else:status='inductive_invariants_pass'
    report=dict(schema=SCHEMA,backend='z3-full-sequence-invariant-induction',status=status,model_semantic_sha256=model_hash(model),checker_sha256=digest(Path(__file__).read_bytes()),solver_version=z.get_version_string(),solver_timeout_ms=solver_timeout_ms,byte_encoding='full_finite_sequence_bv8',prestate_variables='all_typed_values_subject_to_listed_invariants',prestate_timers='active_due_not_before_now',strategy='exact_selected_rule_source_target_constant_substitution_fresh_solver',scope='listed_initial_and_defined_transition_invariants_only',initial_strategy='default_initialization_with_suffix_padding_no_protocol_event',time_advance='time_event_free_invariants_unchanged_between_expiries_atomic_v1_scheduler_trusted',runtime_properties=['positive_timer_duration','active_timer_not_in_past'],invariants=[i['id']for i in model['invariants']],initial_query=initial_query,initial_nonvacuity=initial_enabled,preservation=preservation,overlap=overlap,query_hashes={n:digest(t.encode())for n,t in files.items()},reference_interpreter_called=False,wire_content_proved=False,event_coverage_proved=False,compiler_correctness_proved=False,unbounded_protocol_proof=False,failed_prestate_reachability='not_claimed')
    if out is not None:
        out=Path(out);out.mkdir(parents=True,exist_ok=True)
        for n,t in files.items():(out/n).write_text(t)
        (out/'result.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


def verify(model,out,require_pass=True):
    admitted(model);out=Path(out);report=json.loads((out/'result.json').read_text())
    require(report['schema']==SCHEMA and report['backend']=='z3-full-sequence-invariant-induction','Unsupported induction report')
    require(report['model_semantic_sha256']==model_hash(model)and report['checker_sha256']==digest(Path(__file__).read_bytes()),'Induction source/model changed')
    require(type(report['solver_timeout_ms'])is int and 100<=report['solver_timeout_ms']<=60000,'Induction budget invalid')
    require(report['byte_encoding']=='full_finite_sequence_bv8'and report['prestate_variables']=='all_typed_values_subject_to_listed_invariants'and report['prestate_timers']=='active_due_not_before_now','Induction domains relabelled')
    require(report['strategy']=='exact_selected_rule_source_target_constant_substitution_fresh_solver'and report['scope']=='listed_initial_and_defined_transition_invariants_only','Induction strategy/scope relabelled')
    require(report['initial_strategy']=='default_initialization_with_suffix_padding_no_protocol_event','Initial query scope changed')
    require(report['time_advance']=='time_event_free_invariants_unchanged_between_expiries_atomic_v1_scheduler_trusted'and report['runtime_properties']==['positive_timer_duration','active_timer_not_in_past'],'Induction time/runtime contract changed')
    require(report['invariants']==[i['id']for i in model['invariants']],'Induction property set changed')
    require(all(report[k]is False for k in ('reference_interpreter_called','wire_content_proved','event_coverage_proved','compiler_correctness_proved','unbounded_protocol_proof'))and report['failed_prestate_reachability']=='not_claimed','Induction proof scope falsely broadened')
    require(len(report['preservation'])==len(model['transitions'])and len(report['overlap'])==len(groups(model)),'Induction obligations omitted')
    rows=[report['initial_query'],report['initial_nonvacuity']];names=['initial.smt2','initial-enabled.smt2']
    negative=[report['initial_query']];positive=[report['initial_nonvacuity']]
    for i,(row,rule)in enumerate(zip(report['preservation'],model['transitions'],strict=True)):
        require((row['rule'],row['source'],row['target'])==(rule['id'],rule['from'],rule['to']),'Induction rule correspondence changed')
        rows+=[row['obligation'],row['nonvacuity']];names+=['preserve-'+str(i).zfill(4)+'.smt2','enabled-'+str(i).zfill(4)+'.smt2'];negative.append(row['obligation']);positive.append(row['nonvacuity'])
    for i,(row,(state,event,indices))in enumerate(zip(report['overlap'],groups(model),strict=True)):
        require((row['state'],row['event'],row['rules'])==(state,event,[model['transitions'][j]['id']for j in indices]),'Induction overlap correspondence changed')
        rows.append(row['obligation']);names.append('overlap-'+str(i).zfill(4)+'.smt2');negative.append(row['obligation'])
    require(all(r['query']in ('sat','unsat','unknown')for r in rows),'Invalid solver answer')
    require([r['file']for r in rows]==names and set(report['query_hashes'])==set(names),'Induction query coverage changed')
    require({p.name for p in out.iterdir()if p.is_file()}=={'result.json',*names},'Missing/extra induction files')
    for row,name in zip(rows,names,strict=True):require(row['smt2_sha256']==report['query_hashes'][name]==digest((out/name).read_bytes()),'Induction query changed: '+name)
    if any(r['query']=='sat'for r in negative):actual='inductive_obligation_failure'
    elif any(r['query']=='unknown'for r in negative+positive):actual='unknown'
    elif any(r['query']!='sat'for r in positive):actual='vacuous'
    else:actual='inductive_invariants_pass'
    require(report['status']==actual,'Induction answers falsely promoted')
    if require_pass:require(actual=='inductive_invariants_pass','Induction obligations unresolved/failed')
    return dict(status='valid_inductive_invariant_bindings'if actual=='inductive_invariants_pass'else'valid_unresolved_inductive_bindings',model_semantic_sha256=report['model_semantic_sha256'],preservation_obligations=len(report['preservation']),overlap_obligations=len(report['overlap']),query_files=len(names),fresh_solver_execution=False,source_and_solver_provenance_separately_trusted=True)
