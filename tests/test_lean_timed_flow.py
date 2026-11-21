"""End-to-end admission and retained evidence for a reviewed Lean timed flow."""
import os
from pathlib import Path
import shutil
import tempfile
import unittest

from formal_spec_agent.lean_timed_check import CHECKED, inspect
from protocol_lab.pipeline.runner import STAGES, run, verify
from protocol_lab.pipeline.task import read, sha, write
from flow_diagnostics import record_flow

ROOT = Path(__file__).resolve().parents[1]
MAILBOX = ROOT/'examples/mailbox'
LEAN = os.environ.get('FSA_LEAN') or shutil.which('lean')


class TimedFlowTests(unittest.TestCase):
    def test_reviewed_task_is_required_before_any_proof_execution(self):
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary)/'flow'
            task = MAILBOX/'task.json'
            with self.assertRaisesRegex(ValueError, 'caller-pinned'):
                run(task, MAILBOX, output)
            self.assertFalse(output.exists())

    @unittest.skipUnless(LEAN, 'Pinned Lean required')
    def test_timed_proof_and_native_stages_check_and_bind_their_verdicts(self):
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary)/'flow'
            task_path = MAILBOX/'task.json'
            pin = sha(task_path)
            result = run(task_path, MAILBOX, output, pin)
            diagnostic = record_flow(output, 'timed-mailbox', result)
            self.assertEqual(result['assessment'], 'verified_event_slice', diagnostic)
            self.assertEqual({k: v['status'] for k, v in result['stages'].items()},
                             dict.fromkeys(STAGES, 'pass'))
            formal = result['stages']['formal']['data']
            self.assertEqual((formal['status'], formal['raw_firings']), (CHECKED, 2))
            self.assertEqual(verify(output, MAILBOX, pin)['status'], 'retained_evidence_consistent')

            task = read(task_path)
            manifest = MAILBOX/task['formal']['manifest']
            bundle = output/'stages/formal/queries'
            write(bundle/'result.json', dict(formal, raw_firings=1))
            with self.assertRaisesRegex(ValueError, 'claim or input identity'):
                inspect(bundle, MAILBOX/task['model'], manifest, task['formal']['manifest_sha256'])
