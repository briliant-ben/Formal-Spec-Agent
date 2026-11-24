"""Tests for modular IR composition (`compose`) and parallel proof campaigns (`campaign`)."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import tempfile
import time
import unittest

from formal_spec_agent import campaign, compose as composer
from protocol_lab.ir import load

ROOT = Path(__file__).resolve().parents[1]
TIMED = ROOT / 'examples/lean-timed-efsm'
LEAN = os.environ.get('FSA_LEAN') or shutil.which('lean')
if os.environ.get('FSA_LEAN_REQUIRED') == '1' and not LEAN:
    raise RuntimeError('This CI gate requires the pinned Lean checker; no silent skip')


TIMED_SHARD_SOURCES = {
    'CoreContracts': """import Approved
import TimedObligations

namespace CoreContracts
open Approved FormalSpecAgent TypedMachine TypedIR
open TypedContracts TimedSelection TimedObligations

private theorem initial_valid_checked : TypedContracts.InitialValid model initial := by rfl

private theorem initial_declared_checked : TimerDomain.Declared declaredTimers initial := by
  intro entry member
  change entry ∈ ([] : List TimerEntry) at member
  simp at member

theorem initial_admitted : Approved.initial_admitted :=
  ⟨initial_valid_checked, by decide, initial_declared_checked, by rfl⟩

theorem rule_ids_unique : Approved.rule_ids_unique := by
  unfold Approved.rule_ids_unique Approved.model
  decide

theorem arms_declared : Approved.arms_declared := by
  intro rule member timer delay arm
  rw [model_rules] at member
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;>
    simp_all [declaredTimers, rule_0, rule_1, rule_2, rule_3, rule_4]

theorem timer_coverage : Approved.timer_coverage := by
  intro s _ valid entry inside known
  have id : entry.timer = 0 := List.mem_singleton.mp known
  have active : 0 ∈ s.timers.map TimerEntry.timer :=
    List.mem_map.mpr ⟨entry, inside, id⟩
  have holds : FormalSpecAgent.TypedMachine.eval s zeroValues e30 = true :=
    List.all_eq_true.mp valid e30 (by rw [model_invariants]; simp)
  have hot : s.state = 1 := by
    simpa [TypedMachine.eval, context, e30, e28, e29, TypedIR.eval, TypedIR.equalValue, active] using holds
  refine ⟨rule_4, ?_, hot.symm, ?_, ?_⟩
  · rw [model_rules]; simp
  · rw [id]; rfl
  · rfl

theorem targets_declared : Approved.targets_declared := by
  intro rule member
  rw [model_rules] at member
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;>
    simp [declaredStates, rule_0, rule_1, rule_2, rule_3, rule_4]

theorem raw_catalog_exact : Approved.raw_catalog_exact := by rfl

theorem conflict_catalog_exact : Approved.conflict_catalog_exact := by rfl

end CoreContracts
""",
    'ConflictShard000': """import Approved

namespace ConflictShard000
open Approved FormalSpecAgent TypedMachine TypedIR

private theorem complement (s : Snapshot) (fields : Values) :
    TypedMachine.eval s fields e12 = false ∨ TypedMachine.eval s fields e24 = false := by
  have opposite : TypedMachine.eval s fields e24 = !(TypedMachine.eval s fields e12) := rfl
  rw [opposite]
  cases TypedMachine.eval s fields e12 <;> simp

theorem conflict_0 : Approved.conflict_0 := by
  intro s fields _ left leftIn right rightIn distinct _
  simp [conflictGroup_0] at leftIn rightIn
  rcases leftIn with rfl | rfl <;> rcases rightIn with rfl | rfl
  · exact (distinct rfl).elim
  · exact complement s fields
  · exact Or.symm (complement s fields)
  · exact (distinct rfl).elim

theorem conflict_1 : Approved.conflict_1 := by
  intro s fields _ left leftIn right rightIn distinct _
  simp [conflictGroup_1] at leftIn rightIn
  rcases leftIn with rfl | rfl <;> rcases rightIn with rfl | rfl
  · exact (distinct rfl).elim
  · exact complement s fields
  · exact Or.symm (complement s fields)
  · exact (distinct rfl).elim

end ConflictShard000
""",
    'ConflictShard001': """import Approved

namespace ConflictShard001
open Approved FormalSpecAgent TypedMachine

theorem conflict_2 : Approved.conflict_2 := by
  intro _ _ _ left leftIn right rightIn distinct _
  simp [conflictGroup_2] at leftIn rightIn
  exact (distinct (congrArg Rule.id (leftIn.trans rightIn.symm))).elim

end ConflictShard001
""",
    'FiringShard000': """import Approved
import InvariantFootprint

namespace FiringShard000
open Approved FormalSpecAgent TypedMachine TypedIR TypedContracts TypedFiringContracts

private theorem accepted_raw (r : Rule) (actions : r.actions = rule_0.actions)
    (target : r.target = 1) (guard : r.guard = e12) :
    FiringPreserves model r none := by
  intro s fields _ _ enabledGuard
  have small : ((fields.buffers 0).length : Int) ≤ 16 := by
    rw [guard] at enabledGuard
    change (TypedMachine.eval s fields e7 && decide (((fields.buffers 0).length : Int) ≤ 16)) = true at enabledGuard
    simp only [Bool.and_eq_true, decide_eq_true_eq] at enabledGuard
    exact enabledGuard.2
  unfold candidate
  rw [actions, target]
  simp [rule_0, withoutFiring, work, armTimer, invariantsHold, model_invariants,
    TypedMachine.eval, context, TypedIR.eval, equalValue, getValue, setValue,
    e1, e8, e10, e13, e14, e19, e20, e25, e26, e27, e28, e29, e30, e31,
    e35, small]

private theorem rejected_raw (r : Rule) (actions : r.actions = rule_1.actions)
    (selfLoop : r.target = r.source) :
    FiringPreserves model r none := by
  intro s fields invariant atSource _
  unfold candidate
  rw [selfLoop, ← atSource, actions]
  refine ⟨_, rfl, ?_⟩
  exact invariant

theorem raw_0_external : Approved.raw_0_external :=
  accepted_raw rule_0 rfl rfl rfl

theorem raw_1_external : Approved.raw_1_external :=
  rejected_raw rule_1 rfl rfl

end FiringShard000
""",
    'FiringShard001': """import Approved
import InvariantFootprint

namespace FiringShard001
open Approved FormalSpecAgent TypedMachine TypedIR TypedContracts TypedFiringContracts

private theorem accepted_raw (r : Rule) (actions : r.actions = rule_2.actions)
    (target : r.target = 1) (guard : r.guard = e12) :
    FiringPreserves model r none := by
  intro s fields _ _ enabledGuard
  have small : ((fields.buffers 0).length : Int) ≤ 16 := by
    rw [guard] at enabledGuard
    change (TypedMachine.eval s fields e7 && decide (((fields.buffers 0).length : Int) ≤ 16)) = true at enabledGuard
    simp only [Bool.and_eq_true, decide_eq_true_eq] at enabledGuard
    exact enabledGuard.2
  unfold candidate
  rw [actions, target]
  simp [rule_2, withoutFiring, work, armTimer, invariantsHold, model_invariants,
    TypedMachine.eval, context, TypedIR.eval, equalValue, getValue, setValue,
    e1, e8, e10, e13, e14, e19, e20, e25, e26, e27, e28, e29, e30, e31,
    e35, small]

private theorem rejected_raw (r : Rule) (actions : r.actions = rule_3.actions)
    (selfLoop : r.target = r.source) :
    FiringPreserves model r none := by
  intro s fields invariant atSource _
  unfold candidate
  rw [selfLoop, ← atSource, actions]
  refine ⟨_, rfl, ?_⟩
  exact invariant

theorem raw_2_external : Approved.raw_2_external :=
  accepted_raw rule_2 rfl rfl rfl

theorem raw_3_external : Approved.raw_3_external :=
  rejected_raw rule_3 rfl rfl

end FiringShard001
""",
    'FiringShard002': """import Approved
import InvariantFootprint

namespace FiringShard002
open Approved FormalSpecAgent TypedMachine TypedIR TypedFiringContracts

private theorem expiry_removed (s : Snapshot) :
    0 ∉ (cancelTimer s 0).timers.map TimerEntry.timer := by
  intro active
  obtain ⟨entry, member, eq⟩ := List.mem_map.mp active
  have rejected := (List.mem_filter.mp member).2
  simp [eq] at rejected

theorem raw_4_timer_0 : Approved.raw_4_timer_0 := by
  intro s fields _ _ _
  refine ⟨_, rfl, ?_⟩
  simp [invariantsHold, model_invariants, rule_4, withoutFiring,
    TypedMachine.eval, context, TypedIR.eval, TypedIR.equalValue, getValue, setValue,
    e0, e1, e3, e4, e13, e14, e20, e22, e25, e26, e27, e28, e29, e30,
    e31, e32, e33, e34, e35, e10, expiry_removed]

end FiringShard002
""",
}


def _sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def _write_shard_library(target_dir: Path) -> Path:
    target_dir.mkdir(parents=True, exist_ok=True)
    for mod, src in TIMED_SHARD_SOURCES.items():
        (target_dir / f'{mod}.lean').write_text(src, encoding='utf-8')
    return target_dir


class ComposeAndCampaignTests(unittest.TestCase):
    def test_compose_merges_prefixed_components_and_rejects_conflicts_or_bad_digests(self):
        with tempfile.TemporaryDirectory() as tmp:
            ws = Path(tmp) / 'ws'
            ws.mkdir()
            sub = {
                'requirements': {'REQ': {'source': 's.md#r', 'interpretation': 'one cell'}},
                'variables': {'cnt': {'type': 'int', 'initial': 0}},
                'events': {'go': {'origin': 'application', 'fields': {'d': 'int'}}},
                'messages': {'out': {'fields': {'v': 'int'}}},
                'timers': {'t': {'event': 't_ev'}},
                'transitions': [
                    {
                        'id': 'STEP',
                        'from': 'S0',
                        'to': 'S0',
                        'event': 'go',
                        'guard': {'op': 'ge', 'args': [{'event': 'd'}, 0]},
                        'actions': [
                            {'set': {'var': 'cnt', 'value': {'op': 'add', 'args': [{'var': 'cnt'}, {'event': 'd'}]}}},
                            {'emit': {'message': 'out', 'fields': {'v': {'var': 'cnt'}}}},
                            {'arm': {'timer': 't', 'delay_ms': 100}},
                        ],
                        'requirements': ['REQ'],
                    },
                    {
                        'id': 'EXPIRE',
                        'from': 'S0',
                        'to': 'S0',
                        'event': 't_ev',
                        'guard': True,
                        'actions': [{'set': {'var': 'cnt', 'value': 0}}],
                        'requirements': ['REQ'],
                    },
                ],
                'invariants': [
                    {'id': 'NONNEG', 'assert': {'op': 'ge', 'args': [{'var': 'cnt'}, 0]}, 'requirements': ['REQ']}
                ],
            }
            sub['events']['t_ev'] = {'origin': 'timer', 'fields': {}}
            comp_a = ws / 'a.json'
            comp_b = ws / 'b.json'
            comp_a.write_text(json.dumps(sub))
            comp_b.write_text(json.dumps(sub))
            recipe = ws / 'recipe.json'
            recipe.write_text(json.dumps({
                'schema': 'fsa-compose-v1',
                'protocol': 'two-chan',
                'ir_version': '0.6',
                'semantics': 'flat-efsm-atomic-ordered-v1',
                'states': ['S0'],
                'initial_state': 'S0',
                'scope': {'terminal_states': [], 'excluded': ['toy']},
                'components': [
                    {'id': 'chan_a', 'path': 'a.json', 'sha256': _sha(comp_a), 'prefix': 'a.'},
                    {'id': 'chan_b', 'path': 'b.json', 'sha256': _sha(comp_b), 'prefix': 'b.'},
                ],
            }))
            out_model = ws / 'model.json'
            receipt_path = ws / 'receipt.json'
            receipt = composer.compose(recipe, ws, out_model, receipt_path)
            self.assertEqual(receipt['schema'], 'fsa-compose-receipt-v1')
            self.assertEqual(receipt['counts'], {
                'states': 1, 'variables': 2, 'events': 4, 'messages': 2,
                'timers': 2, 'transitions': 4, 'invariants': 2,
            })
            model = load(out_model)
            self.assertEqual(sorted(model['variables']), ['a.cnt', 'b.cnt'])
            self.assertEqual(sorted(model['timers']), ['a.t', 'b.t'])

            # Tampered component digest must fail.
            comp_b.write_text(json.dumps({**sub, 'invariants': []}))
            with self.assertRaisesRegex(ValueError, 'digest mismatch'):
                composer.compose(recipe, ws, out_model)

            # Unprefixed conflicting variable initial value must fail.
            sub_diff = json.loads(comp_a.read_text())
            sub_diff['variables']['cnt']['initial'] = 1
            comp_b.write_text(json.dumps(sub_diff))
            recipe.write_text(json.dumps({
                'schema': 'fsa-compose-v1',
                'protocol': 'conflict',
                'ir_version': '0.6',
                'semantics': 'flat-efsm-atomic-ordered-v1',
                'states': ['S0'],
                'initial_state': 'S0',
                'scope': {'terminal_states': [], 'excluded': ['toy']},
                'components': [
                    {'id': 'chan_a', 'path': 'a.json', 'sha256': _sha(comp_a)},
                    {'id': 'chan_b', 'path': 'b.json', 'sha256': _sha(comp_b)},
                ],
            }))
            with self.assertRaisesRegex(ValueError, 'Conflicting variables'):
                composer.compose(recipe, ws, out_model)

    def test_campaign_offline_claim_release_and_expired_lease_reclamation(self):
        with tempfile.TemporaryDirectory() as tmp:
            camp = Path(tmp) / 'camp'
            init_res = campaign.init_campaign(
                TIMED, TIMED / 'model.json', camp, skip_precompile=True, shard_size=2, max_attempts=3
            )
            self.assertEqual(init_res['total_units'], 6)
            self.assertEqual(init_res['counts']['pending'], 6)
            self.assertFalse(init_res['ready_to_assemble'])

            claimed_ids = []
            for idx in range(6):
                brief = campaign.claim_unit(camp, f'agent-{idx}', lease_seconds=120)
                self.assertIsNotNone(brief)
                self.assertEqual(brief['schema'], 'fsa-worker-brief-v1')
                self.assertTrue(Path(brief['approved_lean_path']).is_file())
                claimed_ids.append(brief['unit_id'])
            self.assertEqual(len(set(claimed_ids)), 6)
            self.assertIsNone(campaign.claim_unit(camp, 'agent-extra'))

            # Mismatched worker cannot release another worker's claim.
            with self.assertRaisesRegex(ValueError, 'claimed by agent-0'):
                campaign.release_unit(camp, claimed_ids[0], worker_id='wrong-agent')
            rel = campaign.release_unit(camp, claimed_ids[0], worker_id='agent-0')
            self.assertEqual(rel['status'], 'failed')
            reclaimed = campaign.claim_unit(camp, 'agent-replacement')
            self.assertEqual(reclaimed['unit_id'], claimed_ids[0])
            self.assertEqual(reclaimed['attempt'], 2)

            # Expired lease reclamation makes leased unit claimable again.
            state_file = camp / 'campaign.json'
            state = json.loads(state_file.read_text())
            for u in state['units']:
                if u['id'] == claimed_ids[1]:
                    u['lease_expires_at'] = time.time() - 10
            state_file.write_text(json.dumps(state, indent=2) + '\n')
            expired_reclaim = campaign.claim_unit(camp, 'agent-recovery')
            self.assertEqual(expired_reclaim['unit_id'], claimed_ids[1])

    def test_static_screening_blocks_bypasses_and_raw_order_stays_aligned(self):
        # Comment/metaprogramming bypass attempts must be rejected, while bounded recursion limits pass.
        for bad_src in (
            '-- /-\nimport Lean\n',
            '/- comment -/ import Lean\n',
            '/-\n-/ import Lean\n',
            'import Approved\n/- x -/ #eval 1\n',
            'import Approved\nset_option debug.skipKernelTC true\n',
            'import Approved\nnamespace Approved\nend Approved\n',
            'import Approved\ninitialize x : Nat := pure 1\n',
            'import Approved\nelab "hack" : tactic => pure ()\n',
        ):
            with self.subTest(bad_src=bad_src), self.assertRaises(ValueError):
                campaign._validate_candidate_source(bad_src)

        campaign._validate_candidate_source('import Approved\nset_option maxRecDepth 16384\n')

        # Interleaved (from, event) transitions must keep firing shards in exact rawCatalog order.
        with tempfile.TemporaryDirectory() as tmp:
            ws = Path(tmp) / 'ws'
            ws.mkdir()
            interleaved = {
                'ir_version': '0.6',
                'semantics': 'flat-efsm-atomic-ordered-v1',
                'protocol': 'interleaved',
                'scope': {'terminal_states': [], 'excluded': ['toy']},
                'states': ['S0'],
                'initial_state': 'S0',
                'requirements': {'R': {'source': 's.md#r', 'interpretation': 'test'}},
                'variables': {'cnt': {'type': 'int', 'initial': 0}},
                'events': {
                    'evA': {'origin': 'application', 'fields': {}},
                    'evB': {'origin': 'application', 'fields': {}},
                },
                'messages': {},
                'timers': {},
                'transitions': [
                    {'id': 'R0', 'from': 'S0', 'to': 'S0', 'event': 'evA', 'guard': True, 'actions': [], 'requirements': ['R']},
                    {'id': 'R1', 'from': 'S0', 'to': 'S0', 'event': 'evB', 'guard': True, 'actions': [], 'requirements': ['R']},
                    {'id': 'R2', 'from': 'S0', 'to': 'S0', 'event': 'evA', 'guard': True, 'actions': [], 'requirements': ['R']},
                ],
                'invariants': [{'id': 'NONNEG', 'assert': {'op': 'ge', 'args': [{'var': 'cnt'}, 0]}, 'requirements': ['R']}],
            }
            mpath = ws / 'model.json'
            mpath.write_text(json.dumps(interleaved))
            camp = Path(tmp) / 'camp'
            campaign.init_campaign(ws, mpath, camp, skip_precompile=True, shard_size=2)
            st = json.loads((camp / 'campaign.json').read_text())
            self.assertEqual([r['goal'] for r in st['raw_order']], ['raw_0_external', 'raw_1_external', 'raw_2_external'])

    @unittest.skipUnless(LEAN, 'Pinned Lean required')
    def test_campaign_submit_tamper_diagnostic_repair_and_shared_cache(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            shards = _write_shard_library(root / 'shards')
            cache_dir = root / 'shared-cache'
            camp1 = root / 'camp1'
            campaign.init_campaign(TIMED, TIMED / 'model.json', camp1, lean=LEAN, shard_size=2, cache_dir=cache_dir)

            # Reject sorry and disallowed imports before Lean runs.
            bad_sorry = root / 'sorry.lean'
            bad_sorry.write_text('import Approved\ntheorem conflict_2 : Approved.conflict_2 := by sorry\n')
            with self.assertRaisesRegex(ValueError, 'forbidden construct: sorry'):
                campaign.submit_unit(camp1, 'conflict_shard_001', bad_sorry, lean=LEAN)

            bad_import = root / 'bad_imp.lean'
            bad_import.write_text('-- /-\nimport Lean\n')
            with self.assertRaisesRegex(ValueError, 'Disallowed imports'):
                campaign.submit_unit(camp1, 'conflict_shard_001', bad_import, lean=LEAN)

            # Submit failing Lean tactic -> records last_error -> repair succeeds.
            brief = campaign.claim_unit(camp1, 'agent-1', unit_id='conflict_shard_001')
            wrong = root / 'wrong.lean'
            wrong.write_text(
                'import Approved\nnamespace ConflictShard001\n'
                'theorem conflict_2 : Approved.conflict_2 := by exact True.intro\n'
                'end ConflictShard001\n'
            )
            fail_res = campaign.submit_unit(
                camp1, 'conflict_shard_001', wrong, lean=LEAN, worker_id='agent-1', lease_token=brief['lease_token']
            )
            self.assertEqual(fail_res['status'], 'failed')
            self.assertIn('Type mismatch', fail_res['error'])

            retry_brief = campaign.claim_unit(camp1, 'agent-2', unit_id='conflict_shard_001')
            self.assertIn('Type mismatch', retry_brief['last_error'])
            ok_res = campaign.submit_unit(
                camp1, 'conflict_shard_001', shards / 'ConflictShard001.lean',
                lean=LEAN, worker_id='agent-2', lease_token=retry_brief['lease_token']
            )
            self.assertEqual(ok_res['status'], 'verified')
            self.assertIn('conflict_2', ok_res['axioms'])

            # Stale lease token cannot overwrite another worker's reclaimed lease or verified unit.
            stale_brief = campaign.claim_unit(camp1, 'agent-stale', unit_id='firing_shard_000')
            state_path = camp1 / 'campaign.json'
            st = json.loads(state_path.read_text())
            for u in st['units']:
                if u['id'] == 'firing_shard_000':
                    u['lease_expires_at'] = time.time() - 10
            state_path.write_text(json.dumps(st, indent=2) + '\n')
            active_brief = campaign.claim_unit(camp1, 'agent-active', unit_id='firing_shard_000')
            with self.assertRaisesRegex(ValueError, 'Lease token or worker mismatch|no longer active'):
                campaign.submit_unit(
                    camp1, 'firing_shard_000', shards / 'FiringShard000.lean',
                    lean=LEAN, worker_id='agent-stale', lease_token=stale_brief['lease_token']
                )
            self.assertIsNotNone(active_brief)

            # Corrupt shared cache entry for firing_shard_001 must be ignored without burning attempts.
            st2 = json.loads(state_path.read_text())
            f1_key = next(u['cache_key'] for u in st2['units'] if u['id'] == 'firing_shard_001')
            bad_cache_dir = cache_dir / f1_key
            bad_cache_dir.mkdir(parents=True, exist_ok=True)
            bad_bytes = b'import Approved\ntheorem raw_2_external : Approved.raw_2_external := by sorry\n'
            (bad_cache_dir / 'FiringShard001.lean').write_bytes(bad_bytes)
            (bad_cache_dir / 'receipt.json').write_text(json.dumps({
                'cache_key': f1_key, 'module': 'FiringShard001',
                'sha256': hashlib.sha256(bad_bytes).hexdigest(), 'axioms': {},
            }))

            # Second campaign shares cache_dir: conflict_shard_001 hits cache cleanly, corrupt firing_shard_001 still proves via worker.
            camp2 = root / 'camp2'
            campaign.init_campaign(TIMED, TIMED / 'model.json', camp2, lean=LEAN, shard_size=2, cache_dir=cache_dir)
            cmd = f'cp {shards}/{{module}}.lean {{out}}'
            summary = campaign.run_workers(camp2, lean=LEAN, concurrency=4, backend='command', cmd_template=cmd)
            self.assertTrue(summary['ready_to_assemble'])
            self.assertIn('conflict_shard_001', summary['cache_reused'])
            self.assertNotIn('firing_shard_001', summary['cache_reused'])

    @unittest.skipUnless(LEAN, 'Pinned Lean required')
    def test_parallel_command_workers_and_assemble_run_timed_flow(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            shards = _write_shard_library(root / 'shards')
            ws = root / 'timed-ws'
            shutil.copytree(TIMED, ws, ignore=shutil.ignore_patterns('lean'))
            camp = root / 'camp'
            campaign.init_campaign(ws, ws / 'model.json', camp, lean=LEAN, shard_size=2)
            cmd = f'cp {shards}/{{module}}.lean {{out}}'
            summary = campaign.run_workers(camp, lean=LEAN, concurrency=4, backend='command', cmd_template=cmd)
            self.assertEqual(summary['counts']['verified'], 6)
            self.assertTrue(summary['ready_to_assemble'])

            flow_out = root / 'flow-out'
            assembled = campaign.assemble_campaign(
                camp, ws, update_flow='flow.json', run_flow=True, flow_out=flow_out, lean=LEAN
            )
            self.assertEqual(assembled['flow_assessment'], 'verified_event_slice')
            self.assertEqual(assembled['flow_verify'], 'retained_evidence_consistent')
            self.assertTrue((ws / 'lean/TimedProof.lean').is_file())
            self.assertTrue((flow_out / 'stages/generate/generation/protocol.c').is_file())
            self.assertTrue((flow_out / 'stages/build/build/protocol-native').is_file())

    @unittest.skipUnless(LEAN, 'Pinned Lean required')
    def test_provider_backend_feedback_retry_and_uncertain_failure_isolation(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            camp = root / 'camp'
            campaign.init_campaign(TIMED, TIMED / 'model.json', camp, lean=LEAN, shard_size=2, max_attempts=3)
            ledger = root / 'ledger'
            cred = root / 'key'
            cred.write_text('dummy')
            seen_prompts = []

            def fake_provider(messages, ledger_dir, credential_file, **kwargs):
                ledger_dir.mkdir(parents=True, exist_ok=True)
                payload = json.loads(messages[1]['content'])
                seen_prompts.append(payload)
                brief = payload['brief']
                mod = brief['module']
                attempt = sum(1 for p in seen_prompts if p['brief']['module'] == mod)
                if mod == 'ConflictShard001' and attempt == 1:
                    src = 'import Approved\nnamespace ConflictShard001\ntheorem conflict_2 : Approved.conflict_2 := by trivial\nend ConflictShard001\n'
                else:
                    src = TIMED_SHARD_SOURCES[mod]
                fname = hashlib.sha256((mod + str(attempt)).encode()).hexdigest() + '.json'
                (ledger_dir / fname).write_text(json.dumps({'response': {'lean_source': src}}))
                return {'response_file': fname, 'cached': False}

            res = campaign.run_workers(
                camp, lean=LEAN, concurrency=1, backend='provider',
                provider_model='fake-gemini', ledger=ledger, credential_file=cred,
                provider=fake_provider,
            )
            self.assertTrue(res['ready_to_assemble'])
            c1_prompts = [p['brief'] for p in seen_prompts if p['brief']['module'] == 'ConflictShard001']
            self.assertEqual(len(c1_prompts), 2)
            self.assertIsNone(c1_prompts[0]['last_error'])
            self.assertIn('ConflictShard001.lean', c1_prompts[1]['last_error'])
            self.assertIn('error:', c1_prompts[1]['last_error'])

            # Uncertain provider failure halts sibling threads, releases lease, and never silently retries.
            camp2 = root / 'camp2'
            campaign.init_campaign(TIMED, TIMED / 'model.json', camp2, lean=LEAN, shard_size=2)
            calls = []
            import threading
            call_lock = threading.Lock()

            def failing_provider(*args, **kwargs):
                with call_lock:
                    calls.append(1)
                time.sleep(0.05)
                raise TimeoutError('provider uncertainty')

            fail_summary = campaign.run_workers(
                camp2, lean=LEAN, concurrency=2, backend='provider',
                provider_model='fake-gemini', ledger=root / 'ledger2', credential_file=cred,
                provider=failing_provider,
            )
            self.assertLessEqual(len(calls), 2)
            # Even with concurrency=2, abort_provider halts siblings and never retries failed units.
            failed_units = [u for u in fail_summary['units'] if u['status'] == 'failed']
            self.assertTrue(failed_units)
            self.assertTrue(all(u['attempts'] == 1 for u in failed_units))
            self.assertGreaterEqual(fail_summary['counts']['pending'], 4)
            self.assertFalse(fail_summary['ready_to_assemble'])
            self.assertEqual(fail_summary['counts']['claimed'], 0)


if __name__ == '__main__':
    unittest.main()
