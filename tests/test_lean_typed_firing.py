"""Raw timer firing must remove the fired timer before evaluating rule actions."""
import hashlib
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from formal_spec_agent import lean_backend as gate

ROOT=Path(__file__).resolve().parents[1]
LEAN=os.environ.get('FSA_LEAN')or shutil.which('lean')
MODULES=['Foundation','ValueOps','TypedIR','TypedMachine','TypedContracts','TypedFiringContracts']
TARGETS=['FiringPreserves','none_equivalence','eval_clock_irrelevant',
         'invariants_clock_irrelevant','preserving_firing_succeeds','fire_singleton_succeeds']
COUNTERS=['raw_removes_firing_before_actions','runtime_rejects_without_satisfying_raw_property',
          'removing_active_timer_violates_raw_preservation','raw_rearm_uses_current_firing_clock',
          'rearmed_invariant_holds']


class TypedFiringTests(unittest.TestCase):
    def test_timed_spec_is_frozen_before_model_or_oracle(self):
        self.assertEqual(hashlib.sha256((ROOT/'examples/lean-timed-efsm/spec.md').read_bytes()).hexdigest(),
                         '75456866515159edabc2998a97585d1bd891a3c694c83d65f7dd8fbb3f12fdb9')

    def test_unknown_timer_semantics_are_rejected_not_silently_projected(self):
        import copy
        from protocol_lab.ir import load
        from formal_spec_agent.lean_machine import MachineView
        model=load(ROOT/'examples/lean-timed-efsm/model.json')
        model=copy.deepcopy(model);model['timers']['expiry']['duration_ms']=10
        with self.assertRaisesRegex(ValueError,'Unsupported typed machine timer fields'):
            MachineView(model)

    @unittest.skipUnless(LEAN,'Pinned Lean required')
    def test_actual_kernel_firing_bridge_and_counterexample(self):
        with tempfile.TemporaryDirectory()as temporary:
            root=Path(temporary);env=dict(PATH=os.defpath,LEAN_PATH=str(root),LANG='C.UTF-8')
            def compile_module(name):
                return subprocess.run([LEAN,'-o',name+'.olean',name+'.lean'],cwd=root,
                    env=env,capture_output=True,text=True,timeout=60)
            for name in MODULES:
                shutil.copyfile(ROOT/'formal_spec_agent/lean'/(name+'.lean'),root/(name+'.lean'))
                result=compile_module(name)
                self.assertEqual(result.returncode,0,name+'\n'+result.stdout+result.stderr)
            (root/'Audit.lean').write_text('import TypedFiringContracts\n'+''.join(
                '#print axioms FormalSpecAgent.TypedFiringContracts.'+n+'\n'for n in TARGETS))
            result=compile_module('Audit');self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            for n in TARGETS:
                self.assertLessEqual(set(gate.read_axioms(result.stdout,'FormalSpecAgent.TypedFiringContracts.'+n)),gate.AXIOMS)
            shutil.copyfile(ROOT/'tests/lean/TypedFiringContractsAudit.lean',root/'Counterexample.lean')
            result=compile_module('Counterexample');self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            for n in COUNTERS:
                self.assertLessEqual(set(gate.read_axioms(result.stdout,'Controller.'+n)),gate.AXIOMS)
            # A bridge that forgets the actual timer cancellation cannot certify
            # the same runRule or counterexample, even if all external values match.
            source=root/'TypedFiringContracts.lean';s=source.read_text()
            old='candidate snapshot rule fields rule.event firing = .ok t'
            self.assertGreater(s.count(old),0)
            source.write_text(s.replace(old,'candidate snapshot rule fields rule.event none = .ok t'))
            result=compile_module('TypedFiringContracts')
            self.assertNotEqual(result.returncode,0)
            self.assertIn('error:',result.stdout)
