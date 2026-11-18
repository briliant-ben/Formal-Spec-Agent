"""Input-only batch interpreter construction and independent literal comparison."""
from . import lean_machine_native as shared
from .lean_machine_native import input_cases
from .lean_batch import NS,OBS


def render_runtime(view,cases):
    if type(cases)is not list or not 1<=len(cases)<=128:raise ValueError('Batch inputs required')
    source=view.source().replace('namespace Approved\n','namespace MachineRuntime\n',1)+'\nend MachineRuntime\n'
    runner=shared.SERIALIZER.split('def main : IO Unit := do')[0]
    runner+='''def transitionText (t : FormalSpecAgent.BatchObserve.SeenTransition) : String :=
  "{\\\"rule\\\":" ++ toString t.rule ++ ",\\\"event\\\":" ++ toString t.event ++
  ",\\\"fields\\\":" ++ array (t.fields.map pvalue) ++ ",\\\"after\\\":" ++ ss t.after ++
  ",\\\"emitted\\\":" ++ array (t.emitted.map msg) ++ "}"
def batchText : FormalSpecAgent.BatchObserve.Outcome → String
  | .success s trace => "{\\\"status\\\":\\\"ok\\\",\\\"after\\\":" ++ ss s ++
      ",\\\"trace\\\":" ++ array (trace.map transitionText) ++ "}"
  | .error f s => "{\\\"status\\\":\\\"error\\\",\\\"fault\\\":\\\"" ++ faultName f ++
      "\\\",\\\"after\\\":" ++ ss s ++ ",\\\"trace\\\":[]}"

def main : IO Unit := do
'''
    rows=0
    for i,c in enumerate(cases):
        if type(c)is not dict or set(c)!={'id','initial','steps'}or type(c['id'])is not str or type(c['steps'])is not list or not 1<=len(c['steps'])<=128:raise ValueError('Batch runtime accepts inputs only')
        before='s_'+str(i)+'_0';runner+='  let '+before+' := '+view.snapshot(c['initial'])+'\n'
        for j,step in enumerate(c['steps']):
            result='r_'+str(i)+'_'+str(j);command=view.command(step,before).replace(' model ',' MachineRuntime.model ')
            runner+='  let '+result+' := '+command+'\n'
            runner+='  IO.println (batchText ('+OBS+'outcome MachineRuntime.schema MachineRuntime.eventSchemas '+before+' '+result+'))\n'
            after='s_'+str(i)+'_'+str(j+1);runner+='  let '+after+' := '+NS+'rollback '+before+' '+result+'\n';before=after;rows+=1
    if rows>512:raise ValueError('Batch runtime resource limit exceeded')
    return source,runner


def expected_values(view,cases):
    rows=[]
    for case in cases:
        before=case['initial']
        for step in case['steps']:
            e = step['expected']
            if isinstance(e, dict) and e.get('status') == 'error':
                if set(e) == {'status', 'fault', 'after', 'trace'}:
                    if type(e['trace']) is not list or e['trace']:
                        raise ValueError('A failed atomic batch must declare an empty trace')
                    view.expected({'status': 'error', 'fault': e['fault']},
                                  view.snapshot(before), step)
                    after = e['after']
                else:
                    view.expected(e, view.snapshot(before), step)
                    after = before
                rows.append(dict(status='error', fault=e['fault'],
                                 after=shared.canonical_snapshot(view, after), trace=[]))
                continue
            view.expected(e, view.snapshot(before), step)
            trace=[]
            for t in e['trace']:
                event=t['event'];fields=[shared.canonical_value(event['fields'][n],k)for n,k in view.m['events'][event['name']]['fields'].items()]
                ri=next(i for i,r in enumerate(view.m['transitions'])if r['id']==t['rule'])
                trace.append(dict(rule=ri,event=view.events.index(event['name']),fields=fields,after=shared.canonical_snapshot(view,t['after']),emitted=shared.canonical_messages(view,t['emitted'])))
            rows.append(dict(status='ok',after=shared.canonical_snapshot(view,e['after']),trace=trace));before=e['after']
    return rows


def main(argv=None):
    return shared.main(argv,_profile='batch')
