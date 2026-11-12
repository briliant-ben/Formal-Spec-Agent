import concurrent.futures
import copy
import hashlib
import json
from pathlib import Path
import tempfile
import threading
import unittest

from formal_spec_agent.proposals import run as propose
from protocol_lab.pipeline.runner import run, verify
from protocol_lab.pipeline.task import sha, load_task
from protocol_lab.ir import load
from protocol_lab.codegen import render, Unsupported

ROOT = Path(__file__).resolve().parents[1]


class FrameworkTests(unittest.TestCase):
    def test_actual_non_tcp_flow_and_tamper_rejection(self):
        with tempfile.TemporaryDirectory() as tmp:
            workspace = ROOT/'examples/mailbox'
            task = workspace/'task.json'
            out = Path(tmp)/'flow'
            result = run(task, workspace, out, expected_task_sha256=sha(task))
            self.assertEqual(result['assessment'], 'verified_event_slice')
            self.assertEqual(set(result['stages']), {'sources','ir','formal','tests','reference','generate','build','execute','compare','traceability'})
            self.assertFalse(result['protocol_correctness_proved'])
            self.assertEqual(verify(out,workspace,sha(task))['status'],'retained_evidence_consistent')
            path = out/'stages/compare/result.json'
            path.write_text('{}')
            with self.assertRaises(ValueError): verify(out,workspace,sha(task))

    def test_legacy_tcp_wire_adapter_explicitly_refused(self):
        with self.assertRaisesRegex(Unsupported,'not a generic'):
            render(load(ROOT/'examples/mailbox/model.json'), {})
        with tempfile.TemporaryDirectory() as tmp:
            task=json.loads((ROOT/'examples/mailbox/task.json').read_text());task.update(schema='spec-flow-task-v3',wire={'binding':'binding.json','scenarios':[]})
            p=Path(tmp)/'task.json';p.write_text(json.dumps(task))
            with self.assertRaisesRegex(ValueError,'benchmark'):load_task(p,Path(tmp))

    def test_independent_roles_never_self_approve_or_execute_output(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);w=root/'candidate';w.mkdir();(w/'spec.txt').write_text('one fixed rule')
            task=dict(schema='formal-spec-proposal-job-v1',id='test',sources=[dict(path='spec.txt',sha256=sha(w/'spec.txt'))],roles=[dict(id=n,messages=[dict(role='user',content=n)])for n in ('modeler','reviewer')])
            job=w/'job.json';job.write_text(json.dumps(task));calls=[];barrier=threading.Barrier(2)
            def provider(messages,ledger,key,**kw):
                self.assertNotIn(str(key),json.dumps(messages));self.assertIsNone(kw['max_calls']);calls.append(messages)
                barrier.wait(timeout=5)
                ledger.mkdir(exist_ok=True);name=hashlib.sha256(json.dumps(messages).encode()).hexdigest()+'.json';(ledger/name).write_text(json.dumps({'response':{'shell':'do not execute','accepted':True}}));return dict(response_file=name)
            r=propose(job,w,root/'out',root/'private-ledger',root/'secret','fake-model',sha(job),max_calls=None,provider=provider)
            self.assertEqual(len(calls),2);self.assertEqual(r['status'],'requires_controller_review');self.assertFalse(r['protocol_accepted'])
            with self.assertRaises(FileExistsError):propose(job,w,root/'out',root/'private-ledger',root/'secret','fake-model',sha(job),provider=provider)

    def test_provider_failure_not_retried_and_input_changes_reject(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);w=root/'candidate';w.mkdir();source=w/'spec';source.write_text('original')
            task=dict(schema='formal-spec-proposal-job-v1',id='test',sources=[dict(path='spec',sha256=sha(source))],roles=[dict(id='modeler',messages=[dict(role='user',content='propose')])]);job=w/'job';job.write_text(json.dumps(task));calls=[]
            def fail(*args,**kwargs):calls.append(1);raise ValueError('provider incomplete')
            r=propose(job,w,root/'out',root/'ledger',root/'secret','fake',sha(job),provider=fail)
            self.assertEqual(calls,[1]);self.assertEqual(r['status'],'failed_or_uncertain_no_retry')
            source.write_text('mutated')
            with self.assertRaisesRegex(ValueError,'digest'):propose(job,w,root/'out2',root/'ledger',root/'secret','fake',sha(job),provider=fail)
            self.assertEqual(calls,[1])

    def test_source_edit_during_provider_call_invalidates_completed_proposal(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);workspace=root/'candidate';workspace.mkdir();source=workspace/'spec';source.write_text('fixed specification')
            job=workspace/'job.json';job.write_text(json.dumps(dict(schema='formal-spec-proposal-job-v1',id='race',sources=[dict(path='spec',sha256=sha(source))],roles=[dict(id='modeler',messages=[dict(role='user',content='propose')])])) )
            def provider(messages,ledger,key,**kwargs):
                self.assertIn('fixed specification',json.dumps(messages))
                source.write_text('changed during the call')
                ledger.mkdir();(ledger/'answer.json').write_text(json.dumps({'response':{'accepted':True}}))
                return dict(response_file='answer.json')
            result=propose(job,workspace,root/'out',root/'ledger',root/'secret','fake',sha(job),provider=provider)
            self.assertEqual(result['status'],'invalidated_inputs')
            self.assertEqual(result['changed_inputs'],[str(source.resolve())])
            self.assertFalse(result['protocol_accepted'])


if __name__=='__main__':unittest.main()
