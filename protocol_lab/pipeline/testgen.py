"""Generate bounded model-derived witnesses, including explicit IR rejections."""
from collections import deque
import copy
import json
from pathlib import Path
from ..ir import Machine,ModelError,Uncovered,Conflict,evaluate,infer,require
from .task import write


def classification(error):
    if isinstance(error,Conflict):return 'rule_conflict'
    if isinstance(error,Uncovered):return 'model_gap'
    if 'Invariant failed'in str(error):return 'invariant_failure'
    return 'invalid_input_or_model'


def generate(model,config,out,max_prefixes,max_cases):
    out=Path(out);out.mkdir(parents=True,exist_ok=False)
    if set(config)-{'depth','initials','cases'}or type(config['depth'])is not int or not 1<=config['depth']<=12:raise ValueError('Unsupported exploration configuration')
    for c in config['cases']:
        if set(c)-{'states','event','fields','purpose'}:raise ValueError('Unknown input-domain fields')
        require(all(s in model['states']for s in c['states']),'Unknown exploration state')
        schema=model['events'].get(c['event'],{})
        require(schema.get('origin')in ('application','network'),'Timer inputs cannot be injected')
        require(set(c['fields'])==set(schema['fields']),'Exploration field mismatch')
        for name,e in c['fields'].items():require(infer(e,model)==schema['fields'][name],'Exploration type mismatch')
    queue=deque((Machine(model,initial),[],initial)for initial in config['initials'])
    positive=[];negative=[];covered=set();seen_positive=set();seen_negative=set();visited=0;cutoff=0;failures=[]
    while queue and visited<max_prefixes and len(positive)+len(negative)<max_cases:
        machine,path,initial=queue.popleft();visited+=1
        if machine.state in model['scope']['terminal_states']:continue
        if len(path)>=config['depth']:cutoff+=1;continue
        choices=[{'at_ms':machine.now_ms,'event':c['event'],'fields':{k:evaluate(e,machine)for k,e in c['fields'].items()}}
                 for c in config['cases']if machine.state in c['states']]
        if machine.timers:choices.append({'at_ms':min(machine.timers.values()),'tick':True})
        for choice in choices:
            if len(positive)+len(negative)>=max_cases:break
            child=copy.deepcopy(machine)
            try:
                if choice.get('tick'):child.tick(choice['at_ms'])
                else:child.dispatch(choice['event'],choice['fields'],choice['at_ms'])
            except ModelError as error:
                kind=classification(error)
                key=json.dumps([initial,machine.state,choice.get('event'),choice.get('fields'),kind],sort_keys=True)
                if key not in seen_negative:
                    seen_negative.add(key)
                    record=dict(id='negative-'+str(len(negative)),initial=initial,steps=path+[choice],
                                expected_rejection=kind,reference_error=str(error),before=machine.snapshot())
                    negative.append(record)
                    if kind!='model_gap':failures.append(record)
                continue
            for row in child.trace[len(machine.trace):]:
                covered.add(row['transition']);key=(json.dumps(initial,sort_keys=True),row['transition'])
                if key not in seen_positive and len(positive)+len(negative)<max_cases:
                    seen_positive.add(key)
                    case=dict(scenario_version='0.1',id='generated-'+str(len(positive)),initial=initial,
                              steps=path+[choice],expect=dict(state=child.state,variables=child.values,timers=child.timers))
                    name='positive-'+str(len(positive))+'.json';write(out/name,case)
                    positive.append(dict(id=case['id'],file=name,covers=row['transition']))
            queue.append((child,path+[choice],initial))
    write(out/'negative.json',negative)
    result=dict(status='fail'if failures else'pass',classification=failures[0]['expected_rejection']if failures else None,
                positives=positive,negative_file='negative.json',negative_count=len(negative),model_failures=failures,
                visited_prefixes=visited,cutoff_prefixes=cutoff,resource_cutoff=bool(queue),
                declared_depth=config['depth'],covered_rules=sorted(covered),
                uncovered_rules=sorted({r['id']for r in model['transitions']}-covered),
                independent_formal_proof=False,scope='bounded declared-input-domain model-derived witnesses; IR rejection is not RFC behavior acceptance')
    write(out/'result.json',result);return result
