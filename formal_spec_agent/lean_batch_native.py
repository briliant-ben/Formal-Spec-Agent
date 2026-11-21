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

'''
    declarations = []
    operations = ['def main : IO Unit := do']
    rows = 0
    snapshot_type = 'FormalSpecAgent.TypedMachine.Snapshot'
    for i, case in enumerate(cases):
        if (type(case) is not dict or set(case) != {'id', 'initial', 'steps'}
                or type(case['id']) is not str or type(case['steps']) is not list
                or not 1 <= len(case['steps']) <= 128):
            raise ValueError('Batch runtime accepts inputs only')
        # Standalone declarations give each operation its own elaboration budget.
        # Large wire inputs are still rendered with the exact typed values.
        initial = f'initial_{i}'
        declarations.append(f"def {initial} : {snapshot_type} := {view.snapshot(case['initial'])}")
        before = f's_{i}_0'
        operations.append(f'  let {before} := {initial}')
        for j, step in enumerate(case['steps']):
            name = f'command_{i}_{j}'
            body = view.command(step, 'snapshot').replace(' model ', ' MachineRuntime.model ')
            declarations.append(f'def {name} (snapshot : {snapshot_type}) := {body}')
            result = f'r_{i}_{j}'
            operations.append(f'  let {result} := {name} {before}')
            operations.append(
                f'  IO.println (batchText ({OBS}outcome MachineRuntime.schema '
                f'MachineRuntime.eventSchemas {before} {result}))'
            )
            after = f's_{i}_{j+1}'
            operations.append(f'  let {after} := {NS}rollback {before} {result}')
            before = after
            rows += 1
    if rows > 512:
        raise ValueError('Batch runtime resource limit exceeded')
    return source, runner + '\n'.join(declarations + [''] + operations) + '\n'


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
