"""The public proof gate verifies error observations from a frozen oracle."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import tempfile
import unittest

from formal_spec_agent import lean_backend as gate

ROOT = Path(__file__).resolve().parents[1]
EXAMPLE = ROOT / 'examples/lean-timed-efsm'
LEAN = os.environ.get('FSA_LEAN') or shutil.which('lean')


@unittest.skipUnless(LEAN, 'Pinned Lean required')
class TimedReplayTests(unittest.TestCase):
    def test_certificate_rechecks_and_wrong_rollback_is_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            workspace = root / 'workspace'
            shutil.copytree(EXAMPLE, workspace)
            task, proofs = workspace / 'task.json', workspace / 'proofs.json'
            out = root / 'checked'
            result = gate.check(task, workspace, out, proofs, gate.sha(task), LEAN)
            self.assertEqual(result['status'], 'checked_timed_replay', result)
            self.assertEqual(len(result['goals']), 21)
            self.assertEqual(result['axioms'].keys(), set(result['goals']))
            self.assertEqual(gate.verify(out, task, workspace, root / 'rechecked',
                                         gate.sha(task), LEAN)['status'], 'checked_timed_replay')

            oracle = workspace / 'cases.json'
            cases = json.loads(oracle.read_text())
            task_data = json.loads(task.read_text())
            fault = cases[0]['steps'][-1]['expected']
            fault['trace'] = cases[0]['steps'][0]['expected']['trace']
            gate.write(oracle, cases)
            task_data['oracle']['sha256'] = gate.sha(oracle)
            gate.write(task, task_data)
            with self.assertRaisesRegex(ValueError, 'empty trace'):
                gate.prepare(task, workspace, gate.sha(task), draft=True)

            fault['trace'] = []
            fault['after']['now_ms'] += 1
            gate.write(oracle, cases)
            task_data['oracle']['sha256'] = gate.sha(oracle)
            gate.write(task, task_data)
            source, _, _ = gate.prepare(task, workspace, gate.sha(task), draft=True)
            task_data['approved_sha256'] = hashlib.sha256(source.encode()).hexdigest()
            gate.write(task, task_data)
            bad = gate.check(task, workspace, root / 'rejected', proofs, gate.sha(task), LEAN)
            self.assertEqual(bad.get('classification'), 'proof_failure', bad)
            self.assertEqual(bad.get('failed_module'), 'Proofs')
