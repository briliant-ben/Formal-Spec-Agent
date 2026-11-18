"""Kernel-check raw model obligations before the successful scheduler bridges."""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from formal_spec_agent import lean_backend as gate
from formal_spec_agent.lean_batch import BatchView
from protocol_lab.ir import load

ROOT=Path(__file__).resolve().parents[1]
LEAN=os.environ.get('FSA_LEAN')or shutil.which('lean')
MODULES=['Foundation','ValueOps','TypedIR','TypedMachine','TypedContracts',
         'TypedFiringContracts','TimerRank','TimerMinimum','ScheduledPreservation','TimerDomain',
         'TimerEffects','TimerProgress','BatchMachine','BatchReplay','BatchPreservation','TimedSelection','BatchTotality',
         'StoreFacts','MachineObserve','BatchObserve']
TARGETS=['FormalSpecAgent.ScheduledPreservation.'+n for n in [
    'MatchingRaw','fire_success_invariant_from_raw','external_success_invariant_from_raw',
    'timer_success_invariant_from_raw']]+['ScheduledController.raw_obligation_rejects_filtered_timer_loss']


BATCH_TARGETS = [
    *('FormalSpecAgent.TimerDomain.' + name for name in
      ('work_declared', 'fire_declared', 'external_declared', 'step_declared')),
    *('FormalSpecAgent.BatchPreservation.' + name for name in
      ('advance_from_raw', 'tick_from_raw', 'dispatch_from_raw')),
    *('FormalSpecAgent.TimedSelection.' + name for name in
      ('enabled_singleton', 'fire_enabled_from_raw', 'timer_enabled_from_contracts',
       'external_enabled_from_contracts')),
    *('FormalSpecAgent.BatchTotality.' + name for name in
      ('fire_target', 'advance_total', 'tick_total', 'dispatch_total',
       'advance_total_with_timers', 'dispatch_uncovered', 'dispatch_absent',
       'dispatch_success_or_uncovered')),
    'BatchPreservationAudit.undeclared_arm_rejected',
    'BatchPreservationAudit.missing_due_timer_rule_rejected',
]


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
            shutil.copyfile(ROOT/'tests/lean/BatchPreservationAudit.lean',root/'BatchAudit.lean')
            batch = compile_module('BatchAudit')
            self.assertEqual(batch.returncode,0,batch.stdout+batch.stderr)
            for target in BATCH_TARGETS:
                self.assertLessEqual(set(gate.read_axioms(batch.stdout,target)),gate.AXIOMS)
            model = load(ROOT/'examples/lean-timed-efsm/model.json')
            view = BatchView(model)
            initial = dict(state=model['initial_state'], now_ms=0,
                           variables={name: var['initial'] for name, var in model['variables'].items()},
                           timers={})
            approved = view.source(proof_helpers=True).replace(
                'import BatchObserve\n', 'import BatchObserve\nimport BatchTotality\n', 1)
            approved += '\ndef initial : FormalSpecAgent.TypedMachine.Snapshot := ' + view.snapshot(initial)
            approved += '''


def timed_targets_declared : Prop :=
  FormalSpecAgent.BatchTotality.TargetsDeclared model [0, 1]
def timed_initial_valid : Prop :=
  FormalSpecAgent.TypedContracts.InitialValid model initial
def timed_initial_declared : Prop :=
  FormalSpecAgent.TimerDomain.Declared [0] initial
def timed_arms_declared : Prop :=
  FormalSpecAgent.TimerDomain.ArmsDeclared [0] model
def timed_rule_ids_unique : Prop :=
  (model.rules.map FormalSpecAgent.TypedMachine.Rule.id).Nodup
def timed_covers_timers : Prop :=
  FormalSpecAgent.TimedSelection.CoversTimers model [0, 1] [0]

end Approved
'''
            (root/'Approved.lean').write_text(approved)
            approved_result = compile_module('Approved')
            self.assertEqual(approved_result.returncode, 0, approved_result.stdout+approved_result.stderr)
            shutil.copyfile(ROOT/'tests/lean/TimedCellStaticProofs.lean', root/'CellAudit.lean')
            concrete = compile_module('CellAudit')
            self.assertEqual(concrete.returncode, 0, concrete.stdout+concrete.stderr)
            for target in ('initial_valid_checked', 'initial_declared_checked', 'rule_ids_checked',
                           'arms_declared_checked', 'coverage_checked', 'targets_declared_checked',
                           'expiry_raw_checked', 'external_coverage_checked', 'external_raw_checked',
                           'timer_raw_checked', 'guards_disjoint_checked', 'timed_cell_contracts',
                           'timed_cell_start', 'timed_cell_initial_dispatch'):
                self.assertLessEqual(set(gate.read_axioms(concrete.stdout, target)), gate.AXIOMS)
            # Replacing the raw model obligation by True cannot validate this
            # proof chain or the independent timer-loss rejection.
            p=root/'ScheduledPreservation.lean';s=p.read_text()
            old='∀ r ∈ model.rules, r.event = event → FiringPreserves model r firing'
            self.assertEqual(s.count(old),1);p.write_text(s.replace(old,'True'))
            r=compile_module('ScheduledPreservation')
            self.assertNotEqual(r.returncode,0);self.assertIn('error:',r.stdout)

    def test_pinned_tcpip_declared_but_unwired_events(self):
        model_path = os.environ.get('FSA_TCPIP_MODEL')
        if not model_path:
            if os.environ.get('FSA_TCPIP_REQUIRED') == '1':
                self.fail('Pinned TCP/IP model required by this CI channel')
            self.skipTest('Pinned TCP/IP model supplied by dedicated CI')
        source = Path(model_path)
        self.assertEqual(gate.sha(source),
                         '7d5a82541ea55cde3ff39b2e1cf883f6c9f942f5dc535a2736e69044d9e154a5')
        model = load(source)
        self.assertEqual(gate.sha(source),
                         '7d5a82541ea55cde3ff39b2e1cf883f6c9f942f5dc535a2736e69044d9e154a5')
        view = BatchView(model)
        # Independently listed event identities are bound to the actual ordered IR.
        absent = ('T.net.syn', 'T.net.synack', 'T.net.ack', 'T.net.fin',
                  'T.net.rst', 'T.net.rstack', 'T.net.data', 'T.net.packet')
        ids = [view.events.index(name) for name in absent]
        literal = '[' + ', '.join(map(str, ids)) + ']'
        initial = dict(state=model['initial_state'], now_ms=0,
                       variables={name: var['initial'] for name, var in model['variables'].items()},
                       timers={})
        approved = view.source()
        approved += '\ndef initial : FormalSpecAgent.TypedMachine.Snapshot := ' + view.snapshot(initial)
        approved += '\nend Approved\n'
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            env = dict(PATH=os.defpath, LEAN_PATH=str(root), LANG='C.UTF-8')
            for module in MODULES:
                shutil.copyfile(ROOT/'formal_spec_agent/lean'/(module+'.lean'), root/(module+'.lean'))
            (root/'Approved.lean').write_text(approved)
            audit = (ROOT/'tests/lean/TCPIPAbsentExternalAudit.lean').read_text()
            self.assertEqual(audit.count('TCPIP_ABSENT_IDS'), 1)
            (root/'TCPIPAudit.lean').write_text(audit.replace('TCPIP_ABSENT_IDS', literal))
            result = None
            for module in [*MODULES, 'Approved', 'TCPIPAudit']:
                result = subprocess.run([LEAN, '-o', module+'.olean', module+'.lean'],
                    cwd=root, env=env, capture_output=True, text=True, timeout=60)
                self.assertEqual(result.returncode, 0, module+'\n'+result.stdout+result.stderr)
            for name in ('absent_external_exact', 'absent_packet_rolls_back', 'absent_initial_dispatch'):
                self.assertLessEqual(set(gate.read_axioms(result.stdout, 'TCPIPAudit.' + name)),
                                     gate.AXIOMS)
