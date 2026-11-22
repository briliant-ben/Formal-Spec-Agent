"""Controller-owned scheduler tests; fake compiler outputs are never kernel evidence."""
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import threading
import time
from types import SimpleNamespace
import unittest
from unittest.mock import patch
from formal_spec_agent import lean_timed_check as g

FIXTURE = Path(__file__).resolve().parents[1]/'examples/mailbox/model.json'

class FrozenWaves(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.model = self.root/'model.json'
        self.model.write_bytes(FIXTURE.read_bytes())
        self.sources = {'Alpha': 'namespace UnitOnly\ndef alpha := 1\nend UnitOnly\n',
                        'Beta': 'namespace UnitOnly\ndef beta := 2\nend UnitOnly\n',
                        'TimedProof': 'import Alpha\nimport Beta\n'}
        self.tool = self.root/'lean-unit-only'
        self.tool.write_text('fake compiler; never executed')
        self.tool.chmod(0o755)
        self.started, self.finished = [], []
        self.active = self.maximum = 0
        self.lock = threading.Lock()
        self.barrier = None
        self.fail_alpha = False

    def policy(self, version=2, groups=None):
        for name, source in self.sources.items():
            (self.root/(name+'.lean')).write_text(source)
        p = {'schema': f'fsa-lean-timed-proof-manifest-v{version}',
             'model': {'model.json': g.gate.sha(self.model)},
             'modules': [{'module': name, 'sha256': g.gate.sha(self.root/(name+'.lean'))}
                         for name in self.sources]}
        if version == 2:
            p['compile_groups'] = [['Alpha', 'Beta'], ['TimedProof']] if groups is None else groups
        self.manifest = self.root/'manifest.json'
        self.manifest.write_text(json.dumps(p))
        self.pin = g.gate.sha(self.manifest)
        return p

    def fake_run(self, command, **kwargs):
        name = command[-1][:-5]
        with self.lock:
            self.started.append(name)
            self.active += 1
            self.maximum = max(self.maximum, self.active)
            if name == 'TimedProof':
                assert {'Alpha', 'Beta'} <= set(self.finished), 'dependent group started early'
        try:
            if name in ('Alpha', 'Beta') and self.barrier:
                self.barrier.wait(timeout=3)
                time.sleep(.01)
            if name == 'Alpha' and self.fail_alpha:
                raise subprocess.TimeoutExpired(command, 60, output=b'partial unit output')
            return SimpleNamespace(returncode=0, stdout='unit compiler '+name, stderr='')
        finally:
            with self.lock:
                self.finished.append(name)
                self.active -= 1

    def checked(self, folder='out'):
        with patch.object(g.subprocess, 'run', side_effect=self.fake_run), \
             patch.object(g.subprocess, 'check_output', return_value='Lean (version 4.35.0, unit)'), \
             patch.object(g.gate, 'read_axioms', return_value=['propext']):
            result = g.check(self.model, self.manifest, self.pin, self.root/folder, str(self.tool))
        return result

    def inspect(self, result, require_pass=True, folder='out'):
        (self.root/folder/'result.json').write_text(json.dumps(result))
        with patch.object(g.gate, 'read_axioms', return_value=['propext']):
            return g.inspect(self.root/folder, self.model, self.manifest, self.pin, require_pass=require_pass)

    def test_legacy_three_value_api_and_sequential_receipts(self):
        self.policy(version=1)
        self.assertEqual(len(g.proof_inputs(self.model, self.manifest, self.pin)), 3)
        r = self.checked()
        self.assertEqual(r['schema'], 'fsa-lean-timed-check-result-v1')
        self.assertEqual(r['status'], g.CHECKED)
        self.assertEqual(self.maximum, 1)
        self.assertEqual(self.inspect(r), r)

    def test_v2_really_concurrent_and_fully_audited(self):
        self.policy()
        self.assertEqual(len(g.proof_inputs(self.model, self.manifest, self.pin)), 3)
        self.barrier = threading.Barrier(2)
        r = self.checked()
        self.assertEqual(r['status'], g.CHECKED)
        self.assertEqual(r['schema'], 'fsa-lean-timed-check-result-v2')
        self.assertEqual(self.maximum, 2)
        self.assertEqual([x['module'] for x in r['commands']], list(g.MODULES)+['Approved', 'Alpha', 'Beta', 'TimedProof', 'TimedAudit'])
        self.assertEqual(r['compile_groups'], [[n] for n in g.MODULES]+[['Approved'], ['Alpha', 'Beta'], ['TimedProof'], ['TimedAudit']])
        self.assertEqual(self.inspect(r), r)

    def test_failed_parallel_sibling_retained_and_no_later_group(self):
        self.policy()
        self.barrier = threading.Barrier(2)
        self.fail_alpha = True
        r = self.checked()
        self.assertEqual(r['status'], 'fail')
        self.assertEqual(r['classification'], 'resource_unknown')
        self.assertEqual(r['failed_module'], 'Alpha')
        self.assertEqual([x['module'] for x in r['commands']][-2:], ['Alpha', 'Beta'])
        self.assertNotEqual(r['commands'][-2]['returncode'], 0)
        self.assertEqual(r['commands'][-1]['returncode'], 0)
        self.assertNotIn('TimedProof', self.started)
        self.assertNotIn('TimedAudit', self.started)
        self.assertEqual(self.inspect(r, False), r)
        with self.assertRaises(ValueError): self.inspect(r)
        forged = copy.deepcopy(r)
        for suffix in ('stdout', 'stderr'):
            (self.root/'out'/('TimedProof.'+suffix)).write_text('')
        forged['commands'].append({'module': 'TimedProof', 'returncode': 0,
            'stdout_sha256': g.gate.sha(self.root/'out/TimedProof.stdout'),
            'stderr_sha256': g.gate.sha(self.root/'out/TimedProof.stderr')})
        with self.assertRaises(ValueError): self.inspect(forged, False)

    def test_bad_groups_reject_before_compiler_or_output(self):
        cases = [[], [['Alpha'], [], ['Beta'], ['TimedProof']], [['Alpha','Beta','TimedProof']],
                 [['Beta','Alpha'], ['TimedProof']], [['Alpha','Alpha'],['Beta'],['TimedProof']],
                 [['Alpha','Gamma'], ['TimedProof']], [['Alpha',True],['TimedProof']],
                 [['Alpha','Beta']], 'not a list']
        for groups in cases:
            with self.subTest(groups=groups):
                self.policy(groups=groups)
                with patch.object(g.subprocess, 'run') as run:
                    with self.assertRaises((ValueError, TypeError)):
                        g.check(self.model, self.manifest, self.pin, self.root/'rejected', str(self.tool))
                    run.assert_not_called()
                self.assertFalse((self.root/'rejected').exists())

    def test_intra_wave_and_unsupported_imports_reject(self):
        for source in ('import Alpha\n', 'import\n Alpha\n'):
            with self.subTest(source=source):
                self.sources['Beta'] = source
                self.policy()
                with patch.object(g.subprocess, 'run') as run:
                    with self.assertRaises(ValueError):
                        g.check(self.model, self.manifest, self.pin, self.root/'bad-import', str(self.tool))
                    run.assert_not_called()
                self.assertFalse((self.root/'bad-import').exists())

    def test_success_receipt_and_group_tampering_reject(self):
        self.policy()
        self.barrier = threading.Barrier(2)
        r = self.checked()
        changes = []
        x = copy.deepcopy(r); x['commands'] = x['commands'][:-1]; changes.append(x)
        x = copy.deepcopy(r); x['commands'][-2:] = reversed(x['commands'][-2:]); changes.append(x)
        x = copy.deepcopy(r); x['commands'].append(x['commands'][-1]); changes.append(x)
        x = copy.deepcopy(r); x['compile_groups'][-3] = ['Beta','Alpha']; changes.append(x)
        x = copy.deepcopy(r); x['axioms']['initial'] = ['unapproved']; changes.append(x)
        for i, changed in enumerate(changes):
            with self.subTest(index=i):
                with self.assertRaises(ValueError): self.inspect(changed)
        self.inspect(r)
        (self.root/'out/Alpha.stdout').write_text('changed after compilation')
        with self.assertRaises(ValueError): self.inspect(r)

    def test_receipt_boolean_and_numeric_aliases_reject(self):
        self.policy()
        self.barrier = threading.Barrier(2)
        r = self.checked()
        for code in (False, 0.0):
            changed = copy.deepcopy(r)
            changed['commands'][0]['returncode'] = code
            with self.assertRaises(ValueError): self.inspect(changed)
        for key, value in [('raw_firings', 2.0), ('compiler_correctness_proved', 0)]:
            changed = copy.deepcopy(r)
            changed[key] = value
            with self.assertRaises(ValueError): self.inspect(changed)

if __name__ == '__main__': unittest.main(verbosity=2)
