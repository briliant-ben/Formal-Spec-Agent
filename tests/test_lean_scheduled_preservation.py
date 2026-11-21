"""Kernel-check raw model obligations before the successful scheduler bridges."""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from formal_spec_agent import lean_backend as gate
from formal_spec_agent.lean_timed_contracts import render
from protocol_lab.ir import load

ROOT=Path(__file__).resolve().parents[1]
LEAN=os.environ.get('FSA_LEAN')or shutil.which('lean')
MODULES=['Foundation','ValueOps','SequenceFacts','OctetFacts','TypedIR','OctetBounds','TypedMachine','TypedContracts',
         'TypedFiringContracts','TimerRank','TimerMinimum','ScheduledPreservation','TimerDomain',
         'TimerEffects','TimerProgress','BatchMachine','BatchReplay','BatchPreservation','TimedSelection','BatchTotality',
         'StoreFacts','MachineObserve','BatchObserve','TimedObligations','GuardDiscriminators','InvariantFootprint','ResetPreservation','TimerInvariantFacts',
         'ExprRewrite','EffectFootprint','GuardedSuffix','EffectConditions']
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
            shutil.copyfile(ROOT/'tests/lean/EffectConditionsAudit.lean', root/'EffectsAudit.lean')
            effects = compile_module('EffectsAudit')
            self.assertEqual(effects.returncode, 0, effects.stdout + effects.stderr)
            for theorem in ('ordered_firing', 'wrong_order_rejected', 'footprint_separates_reads',
                            'octet_bound_sound', 'octet_lower_bound', 'octet_minimum_count_bound',
                            'octet_bound_rejects_insufficient_information'):
                self.assertLessEqual(set(gate.read_axioms(effects.stdout, 'EffectConditionsAudit.' + theorem)),
                                     gate.AXIOMS)
            model = load(ROOT/'examples/lean-timed-efsm/model.json')
            approved, goals = render(model)
            self.assertEqual(len(goals), 16)
            (root/'Approved.lean').write_text(approved)
            approved_result = compile_module('Approved')
            self.assertEqual(approved_result.returncode, 0, approved_result.stdout+approved_result.stderr)
            shutil.copyfile(ROOT/'tests/lean/TimedCellStaticProofs.lean', root/'CellAudit.lean')
            concrete = compile_module('CellAudit')
            self.assertEqual(concrete.returncode, 0, concrete.stdout+concrete.stderr)
            for target in ('initial_valid_checked', 'initial_declared_checked', 'rule_ids_checked',
                           'arms_declared_checked', 'coverage_checked', 'targets_declared_checked',
                           'expiry_raw_checked', 'external_coverage_checked', 'raw_catalog_checked',
                           'conflict_catalog_checked', 'raw_checks', 'conflicts_checked', 'timed_cell_contracts',
                           'timed_cell_start', 'timed_cell_initial_dispatch'):
                self.assertLessEqual(set(gate.read_axioms(concrete.stdout, target)), gate.AXIOMS)
            dropped = '''import Approved
import GuardDiscriminators
import InvariantFootprint
import ResetPreservation
import TimerInvariantFacts
open Approved FormalSpecAgent.TimedObligations FormalSpecAgent.GuardDiscriminators
open FormalSpecAgent.TypedIR
example : rawChecks model declaredTimers ≠ rawCatalog.dropLast := by
  intro wrong
  cases wrong
example : conflictChecks model ≠ conflictCatalog.dropLast := by
  intro wrong
  cases wrong

def yes : Expr .boolean := .equal .boolean (.variable .boolean 0) (.literal .boolean true)
def no : Expr .boolean := .equal .boolean (.variable .boolean 0) (.literal .boolean false)
def fieldNo : Expr .boolean := .equal .boolean (.field .boolean 0) (.literal .boolean false)
example : separated (facts yes) (facts no) = true := rfl
example : separated (facts yes) (facts fieldNo) = false := rfl
example : separated (facts yes) (facts (.boolOr no (.literal .boolean true))) = false := rfl

def variableFlag : Expr .boolean := .variable .boolean 0
def fieldFlag : Expr .boolean := .field .boolean 0
example : separated (facts variableFlag) (facts (.boolNot variableFlag)) = true := rfl
example : separated (facts fieldFlag) (facts fieldNo) = true := rfl
example : separated (facts variableFlag) (facts (.boolNot fieldFlag)) = false := rfl

-- Use a clipped byte view. Comparing the same read at an inclusive boundary
-- is insufficient unless the bounds are strictly separated.
def firstByte : Expr .integer :=
  .byteAt (.slice (.field .octets 0) (.literal .integer 5) (.literal .integer 2)) (.literal .integer 0)
def upper (n : Int) : Expr .boolean := .intLe firstByte (.literal .integer n)
def lower (n : Int) : Expr .boolean := .intGe firstByte (.literal .integer n)
example : separated (facts (upper 23)) (facts (lower 24)) = true := rfl
example : separated (facts (upper 23)) (facts (lower 23)) = false := rfl
example : separated (facts (lower 24)) (facts (.boolNot (lower 24))) = true := rfl
example : separated (facts (upper (-1))) (facts (.boolNot (upper (-1)))) = true := rfl
example : separated (facts (.equal .integer firstByte (.literal .integer 23)))
    (facts (.notEqual .integer firstByte (.literal .integer 23))) = true := rfl

example : separated (facts (.boolOr (upper 23) (.literal .boolean true))) (facts (lower 24)) = false := rfl

def constant (n : Int) : Expr .integer := .literal .integer n
def frame : Expr .octets := .field .octets 0
def ip : Expr .octets := .slice frame (constant 14) (constant 20)
def protocol : Expr .octets := .slice ip (constant 9) (constant 1)
def tcp : Expr .boolean := .equal .integer (.byteAt frame (constant 23)) (constant 6)
def udp : Expr .boolean := .equal .octets protocol (.literal .octets [⟨17, by decide⟩])
def icmp : Expr .boolean := .equal .integer (.byteAt ip (constant 9)) (constant 1)

example : separated (facts udp) (facts tcp) = true := rfl
example : separated (facts tcp) (facts icmp) = true := rfl

-- A zero read from a clipped slice supplies no absolute byte fact.
def clipped : Expr .octets := .slice ip (constant 9) (constant 0)
def clippedZero : Expr .boolean := .equal .integer (.byteAt clipped (constant 0)) (constant 0)
def emptySlice : Expr .boolean := .equal .octets clipped (.literal .octets [])
example : separated (facts clippedZero) (facts tcp) = false := rfl
example : separated (facts emptySlice) (facts tcp) = false := rfl

def checksum : Expr .integer := .checksum (.concat (.pack16 (constant 20)) ip)
def validChecksum : Expr .boolean := .equal .integer checksum (constant 0)
def validLength : Expr .boolean :=
  .equal .integer (.add (constant 14) (.bytesLength ip)) (.bytesLength frame)
example : separated (facts validChecksum) (facts (.boolNot validChecksum)) = true := rfl
example : separated (facts validLength) (facts (.boolNot validLength)) = true := rfl
example : separated (facts validLength)
    (facts (.notEqual .integer (.add (constant 14) (.bytesLength ip)) (constant 60))) = false := rfl
example : separated (facts udp) (facts (.boolNot udp)) = true := rfl

def ipTotal : Expr .integer := .field .integer 0
def physicalLength : Expr .integer := .bytesLength frame
def plainLength : Expr .integer := .add (constant 14) ipTotal
def paddedLength (size : Int) : Expr .integer :=
  .choose .integer (.intLe ipTotal (constant 46)) (constant size) plainLength

def accepted (padding : Int) : Expr .boolean :=
  .boolAnd (.intGe ipTotal (constant 40))
    (.boolOr (.equal .integer physicalLength (paddedLength padding))
      (.equal .integer physicalLength plainLength))

def malformed : Expr .boolean :=
  .boolOr (.intLe ipTotal (constant 39)) (.intGe ipTotal (.sub physicalLength (constant 13)))

def wireRule (id : Nat) (guard : Expr .boolean) : FormalSpecAgent.TypedMachine.Rule :=
  { id := id, event := 0, source := 0, target := 0, guard := guard, actions := [] }

example : residualPairs [wireRule 0 (accepted 60), wireRule 1 malformed] = [] := rfl
-- With total length 46, a 59-byte frame could satisfy both guards.
example : (residualPairs [wireRule 0 (accepted 59), wireRule 1 malformed]).length = 1 := rfl

def floored (cutoff padding : Int) (retained : Expr .integer) : Expr .boolean :=
  .equal .integer physicalLength
    (.choose .integer (.intGe plainLength (constant cutoff)) retained (constant padding))

def tooShort : Expr .boolean := .intGe plainLength (.add physicalLength (constant 1))
example : separated (facts (floored 60 60 plainLength)) (facts tooShort) = true := rfl
-- A cutoff above the padding, or a different retained expression, need not bound the frame.
example : separated (facts (floored 61 59 plainLength)) (facts tooShort) = false := rfl
example : separated (facts (floored 60 60 ipTotal)) (facts tooShort) = false := rfl

def serialBase : Expr .sequence := .variable .sequence 0
def serialAck : Expr .sequence := .field .sequence 0
def halfSpace : Expr .boolean :=
  .equal .integer (.seqDistance serialBase serialAck) (constant 2147483648)

example : FormalSpecAgent.InvariantFootprint.ignoresSlot 0 (.variable .integer 0) = false := rfl
example : FormalSpecAgent.InvariantFootprint.ignoresSlot 0 (.field .integer 0) = true := rfl

example : separated (facts (.seqLt serialBase serialAck)) (facts (.seqLt serialAck serialBase)) = true := rfl
example : separated (facts (.seqComparable serialBase serialAck)) (facts halfSpace) = true := rfl
example : separated (facts (.seqLe serialBase serialAck))
    (facts (.equal .sequence serialAck serialBase)) = false := rfl
example : separated (facts (.equal .sequence serialAck serialBase))
    (facts (.notEqual .sequence serialBase serialAck)) = true := rfl

-- Rewriting a watched store slot to its current value requires an unconditional
-- fact about the store. A disjunction or the event field cannot supply it.
def exampleState : Expr .text := .variable .text 0
def exampleText : Expr .text := .literal .text "READY"
def exampleGuard : Expr .boolean := .equal .text exampleState exampleText
def exampleModel : FormalSpecAgent.TypedMachine.Model :=
  { rules := [], invariants := [exampleGuard], externalEvents := [], timerEvents := id }
def writeCurrent : FormalSpecAgent.TypedMachine.Action := .assign .text 0 exampleText
open FormalSpecAgent.InvariantFootprint in
example : guardedEffect exampleModel (.boolAnd (.literal .boolean true) exampleGuard) writeCurrent
    = true := by decide +kernel
open FormalSpecAgent.InvariantFootprint in
example : guardedEffect exampleModel (.boolOr (.literal .boolean true) exampleGuard) writeCurrent
    = false := by decide +kernel
open FormalSpecAgent.InvariantFootprint in
example : guardedEffect exampleModel (.equal .text (.field .text 0) exampleText) writeCurrent
    = false := by decide +kernel
open FormalSpecAgent.InvariantFootprint in
example : guardedEffect exampleModel exampleGuard (.assign .text 0 (.literal .text "OTHER"))
    = false := by decide +kernel

-- Recognize an empty buffer reset only when its guard is unaffected and
-- later effects preserve the empty buffer. A timer firing has different semantics.
open FormalSpecAgent.TypedMachine FormalSpecAgent.ResetPreservation in
def resetExample (bound : Int) (guard : Expr .boolean) (tail : List Action) (external : Bool) : Model :=
  { rules := [{ id := 0, event := 0, source := 0, target := 0, guard := guard,
                actions := .assign .octets 0 (.literal .octets []) :: tail }],
    invariants := [.intLe (.bytesLength (.variable .octets 0)) (constant bound)],
    externalEvents := if external then [0] else [],
    timerEvents := id }

open FormalSpecAgent.ResetPreservation in
example : (resetChecks (resetExample 2 (.literal .boolean true) [] true) []).length = 1 := by
  decide +kernel
open FormalSpecAgent.ResetPreservation in
example : (resetChecks (resetExample (-1) (.literal .boolean true) [] true) []).length = 0 := by
  decide +kernel
open FormalSpecAgent.ResetPreservation in
example : (resetChecks (resetExample 2 (.equal .octets (.variable .octets 0) (.literal .octets []))
    [] true) []).length = 0 := by decide +kernel
open FormalSpecAgent.ResetPreservation in
example : (resetChecks (resetExample 2 (.literal .boolean true)
    [.assign .octets 0 (.literal .octets [⟨1, by decide⟩])] true) []).length = 0 := by
  decide +kernel
open FormalSpecAgent.ResetPreservation in
example : (resetChecks (resetExample 2 (.literal .boolean true) [] false) [0]).length = 0 := by
  decide +kernel

-- Rearming the current owner replaces all of its old entries, retains a
-- different owner at the same deadline, and preserves activity for both.
open FormalSpecAgent.TypedMachine in
def rearmBefore : Snapshot :=
  { values := zeroValues, state := 0, now := 100, timers := [⟨1, 100⟩, ⟨2, 100⟩, ⟨1, 101⟩] }
open FormalSpecAgent.TypedMachine in
def rearmAfter : Snapshot := { rearmBefore with timers := [⟨2, 100⟩, ⟨1, 1100⟩] }
open FormalSpecAgent.TypedMachine in
def activeModel : Model :=
  { rules := [], invariants := [.timerActive 1, .timerActive 2], externalEvents := [], timerEvents := id }
open FormalSpecAgent.TypedMachine FormalSpecAgent.TimerInvariantFacts in
example : invariantsHold activeModel rearmAfter = true :=
  rearmed_invariants activeModel rearmBefore rearmAfter 1 1000 (by decide +kernel)
    rfl (by decide +kernel)
open FormalSpecAgent.TypedMachine in
example : invariantsHold activeModel (cancelTimer rearmBefore 1) = false := by decide +kernel

def maxSerial : Expr .sequence := .literal .sequence ⟨4294967295, by decide⟩
def zeroSerial : Expr .sequence := .literal .sequence 0
example (ctx : Context) : eval (.seqLt maxSerial zeroSerial) ctx = true := rfl
example (ctx : Context) : eval (.seqLt zeroSerial maxSerial) ctx = false := by
  open FormalSpecAgent.ValueOps in
  change seqLt 0 ⟨4294967295, by decide⟩ = false
  unfold FormalSpecAgent.ValueOps.seqLt
  apply decide_eq_false
  intro ordered
  have distance : FormalSpecAgent.ValueOps.seqDistance 0 ⟨4294967295, by decide⟩ = 4294967295 := by
    change (4294967295 : Int) % 4294967296 = 4294967295
    exact Int.emod_eq_of_lt (by omega) (by omega)
  rw [distance] at ordered
  omega





'''
            (root/'Dropped.lean').write_text(dropped)
            rejected = compile_module('Dropped')
            self.assertEqual(rejected.returncode, 0, rejected.stdout + rejected.stderr)
            # Replacing the raw model obligation by True cannot validate this
            # proof chain or the independent timer-loss rejection.
            p=root/'ScheduledPreservation.lean';s=p.read_text()
            old='∀ r ∈ model.rules, r.event = event → FiringPreserves model r firing'
            self.assertEqual(s.count(old),1);p.write_text(s.replace(old,'True'))
            r=compile_module('ScheduledPreservation')
            self.assertNotEqual(r.returncode,0);self.assertIn('error:',r.stdout)

    def test_pinned_tcpip_catalogs_conflict_groups_and_unwired_events(self):
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
        # Independently listed event identities are bound to the actual ordered IR.
        absent = ('T.net.syn', 'T.net.synack', 'T.net.ack', 'T.net.fin',
                  'T.net.rst', 'T.net.rstack', 'T.net.data', 'T.net.packet')
        ids = [list(model['events']).index(name) for name in absent]
        literal = '[' + ', '.join(map(str, ids)) + ']'
        approved, goals = render(model)
        self.assertEqual(sum(name.startswith('raw_') for name in goals), 336)  # 335 clauses plus equality
        self.assertEqual(sum(name.startswith('conflict_') for name in goals), 19)  # 18 groups plus equality
        # Match the audit's numeric layer partition to actual IR rule names.
        frame_rules = [(index, row) for index, row in enumerate(model['transitions'])
                       if row['event'] == 'L.net.frame']
        self.assertEqual(len(frame_rules), 239)
        self.assertEqual(model['transitions'][334]['id'], 'T.WIRE-DROP-IP-LENGTH-MALFORMED')
        self.assertIn(334, {index for index, _ in frame_rules})
        for index, row in frame_rules:
            self.assertTrue(row['id'].startswith('L.' if index < 64 else 'T.'), row['id'])

        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            env = dict(PATH=os.defpath, LEAN_PATH=str(root), LANG='C.UTF-8')
            for module in MODULES:
                shutil.copyfile(ROOT/'formal_spec_agent/lean'/(module+'.lean'), root/(module+'.lean'))
            (root/'Approved.lean').write_text(approved)
            audit = (ROOT/'tests/lean/TCPIPTimedAudit.lean').read_text()
            self.assertEqual(audit.count('TCPIP_ABSENT_IDS'), 1)
            (root/'TCPIPAudit.lean').write_text(audit.replace('TCPIP_ABSENT_IDS', literal))
            tcpip_modules = (
                'TCPIPFrameCatalog', 'TCPIPFramePairs', 'TCPIPTimerRules', 'TCPIPQueries',
                'TCPIPCacheConfig', 'TCPIPUDPDeliver', 'TCPIPSendQueue', 'TCPIPEmptyResponses',
                'TCPIPApplicationRead', 'TCPIPApplicationReadEmpty', 'TCPIPAcknowledgments',
                'TCPIPReceiveData', 'TCPIPSendWire', 'TCPIPRetransmit',
                'TCPIPTransmitFacts', 'TCPIPTransmit', 'TCPIPQueueRelease', 'TCPIPClosedTransitions',
                'TCPIPControlReplies', 'TCPIPArpLearn', 'TCPIPIcmpReply', 'TCPIPUdpSend',
                'TCPIPOpen', 'TCPIPTimerCoverage', 'TCPIPTimerContracts',
            )
            for module in tcpip_modules:
                shutil.copyfile(ROOT/'tests/lean'/(module+'.lean'), root/(module+'.lean'))
            blocks = [f'FrameBlock{index}' for index in range(16)]
            expected = {
                5: '(TCPIPFramePairs.control.take 3).map TCPIPFrameCatalog.pairId',
                6: '(TCPIPFramePairs.control.drop 3).map TCPIPFrameCatalog.pairId',
                10: '(TCPIPFramePairs.data.take 13).map TCPIPFrameCatalog.pairId',
                11: '(TCPIPFramePairs.data.drop 13).map TCPIPFrameCatalog.pairId',
            }
            for index, block in enumerate(blocks):
                (root/f'{block}.lean').write_text(
                    'import TCPIPFramePairs\n'
                    'set_option maxRecDepth 65536 in\n'
                    'set_option maxHeartbeats 8000000 in\n'
                    f'theorem frameBlock{index} : TCPIPFrameCatalog.blockIds {index} = '
                    f'{expected.get(index, "[]")} := by decide +kernel\n')
            (root/'FrameCatalogExact.lean').write_text(
                ''.join(f'import {block}\n' for block in blocks)
                + 'open FormalSpecAgent.GuardDiscriminators Approved TCPIPFrameCatalog\n'
                + 'set_option maxRecDepth 16384 in\n'
                + 'theorem frameCatalogExact : (residualPairs conflictGroup_4).map pairId = '
                + '(TCPIPFramePairs.control ++ TCPIPFramePairs.data).map pairId := by\n'
                + '  rw [TCPIPFrameCatalog.merge_blocks, '
                + ', '.join(f'frameBlock{index}' for index in range(len(blocks))) + ']\n'
                + '  simp only [List.nil_append, List.append_nil, ← List.map_append, '
                + 'List.append_assoc, List.take_append_drop]\n')

            result = None
            for module in [*MODULES, 'Approved', *tcpip_modules, *blocks, 'FrameCatalogExact', 'TCPIPAudit']:
                result = subprocess.run([LEAN, '-o', module+'.olean', module+'.lean'],
                    cwd=root, env=env, capture_output=True, text=True, timeout=60)
                self.assertEqual(result.returncode, 0, module+'\n'+result.stdout+result.stderr)
            for name in ('count', 'exact_catalog'):
                self.assertLessEqual(set(gate.read_axioms(result.stdout, 'TCPIPTimerContracts.' + name)),
                                     gate.AXIOMS)
            for name in ('absent_external_exact', 'absent_packet_rolls_back',
                         'absent_initial_dispatch', 'closed_groups', 'frame_group', 'malformed_length_preserves',
                         'send_group', 'transmit_group', 'endpoint_guarded_count', 'endpoint_guarded_preservation',
                         'endpoint_reset_count', 'endpoint_preservation_count', 'endpoint_preservation_unique',
                         'endpoint_preservation_checked', 'endpoint_query_retry_obligation', 'endpoint_arp_members', 'endpoint_udp_members', 'endpoint_send_member', 'endpoint_tcp_response_members', 'endpoint_tcp_read_members', 'endpoint_ack_members', 'endpoint_receive_members',
                         'endpoint_retransmit_members', 'endpoint_transmit_members', 'endpoint_closed_transition_members',
                         'endpoint_control_reply_members', 'endpoint_arp_learn_members',
                         'endpoint_icmp_reply_members', 'endpoint_udp_send_members',
                         'endpoint_open_members', 'endpoint_initial_admitted', 'endpoint_timer_contract', 'endpoint_timer_batch', 'endpoint_absent_dispatch',
                         'endpoint_raw_exact', 'endpoint_raw_count', 'endpoint_conflicts_exact', 'endpoint_guards_disjoint'):
                self.assertLessEqual(set(gate.read_axioms(result.stdout, 'TCPIPAudit.' + name)),
                                     gate.AXIOMS)
