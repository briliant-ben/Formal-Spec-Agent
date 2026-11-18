"""Kernel-check raw model obligations before the successful scheduler bridges."""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from formal_spec_agent import lean_backend as gate

ROOT=Path(__file__).resolve().parents[1]
LEAN=os.environ.get('FSA_LEAN')or shutil.which('lean')
MODULES=['Foundation','ValueOps','TypedIR','TypedMachine','TypedContracts',
         'TypedFiringContracts','TimerRank','TimerMinimum','ScheduledPreservation']
TARGETS=['FormalSpecAgent.ScheduledPreservation.'+n for n in [
    'MatchingRaw','fire_success_invariant_from_raw','external_success_invariant_from_raw',
    'timer_success_invariant_from_raw']]+['ScheduledController.raw_obligation_rejects_filtered_timer_loss']


@unittest.skipUnless(LEAN,'Pinned Lean required')
class ScheduledPreservationTests(unittest.TestCase):
    def test_kernel_raw_bridge_and_negative_model_obligation(self):
        with tempfile.TemporaryDirectory()as temporary:
            root=Path(temporary);env=dict(PATH=os.defpath,LEAN_PATH=str(root),LANG='C.UTF-8')
            def compile_module(name):
                return subprocess.run([LEAN,'-o',name+'.olean',name+'.lean'],cwd=root,
                    env=env,capture_output=True,text=True,timeout=60)
            for name in MODULES:
                shutil.copyfile(ROOT/'formal_spec_agent/lean'/(name+'.lean'),root/(name+'.lean'))
                r=compile_module(name);self.assertEqual(r.returncode,0,name+'\n'+r.stdout+r.stderr)
            shutil.copyfile(ROOT/'tests/lean/TypedFiringContractsAudit.lean',root/'Counterexample.lean')
            r=compile_module('Counterexample');self.assertEqual(r.returncode,0,r.stdout+r.stderr)
            shutil.copyfile(ROOT/'tests/lean/ScheduledPreservationAudit.lean',root/'Audit.lean')
            r=compile_module('Audit');self.assertEqual(r.returncode,0,r.stdout+r.stderr)
            for name in TARGETS:self.assertLessEqual(set(gate.read_axioms(r.stdout,name)),gate.AXIOMS)
            # Replacing the raw model obligation by True cannot validate this
            # proof chain or the independent timer-loss rejection.
            p=root/'ScheduledPreservation.lean';s=p.read_text()
            old='∀ r ∈ model.rules, r.event = event → FiringPreserves model r firing'
            self.assertEqual(s.count(old),1);p.write_text(s.replace(old,'True'))
            r=compile_module('ScheduledPreservation')
            self.assertNotEqual(r.returncode,0);self.assertIn('error:',r.stdout)
