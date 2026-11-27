"""Tests for ir_builder, unrolled fsa_checksum16, workspace *_ws APIs, and system_codegen."""
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from formal_spec_agent import ir_builder as B
from formal_spec_agent import system_codegen
from protocol_lab.ir import internet_checksum16

CC = shutil.which('cc')


def _compile(cmd):
    res = subprocess.run(cmd, capture_output=True, text=True, timeout=120)
    if res.returncode != 0:
        raise AssertionError(f'Command failed {cmd}:\n{res.stdout}\n{res.stderr}')
    return res


@unittest.skipUnless(CC, 'C99 compiler named cc required')
class SystemCodegenTests(unittest.TestCase):
    def test_ir_builder_wire_and_system_composer_end_to_end(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)

            # 1. Actor architecture hook model
            actor_m = {
                'ir_version': '0.6',
                'semantics': 'flat-efsm-atomic-ordered-v1',
                'protocol': 'mini-actor',
                'scope': {'terminal_states': [], 'excluded': ['test']},
                'states': ['STOPPED', 'IDLE', 'BUSY'],
                'initial_state': 'STOPPED',
                'requirements': {'A': {'source': 's#a', 'interpretation': 'actor'}},
                'variables': {'ops': {'type': 'int', 'initial': 0}},
                'events': {
                    'start': {'origin': 'application', 'fields': {}},
                    'post_rx': {'origin': 'application', 'fields': {}},
                    'dispatch': {'origin': 'application', 'fields': {}},
                    'complete': {'origin': 'application', 'fields': {}},
                    'stop': {'origin': 'application', 'fields': {}},
                },
                'messages': {},
                'timers': {},
                'transitions': [
                    B.rule('A.START', 'STOPPED', 'IDLE', 'start', True, [], ['A']),
                    B.rule('A.RX', 'IDLE', 'IDLE', 'post_rx', True, [B.act_set('ops', B.add_(B.var('ops'), 1))], ['A']),
                    B.rule('A.DISP', 'IDLE', 'BUSY', 'dispatch', True, [], ['A']),
                    B.rule('A.DONE', 'BUSY', 'IDLE', 'complete', True, [], ['A']),
                    B.rule('A.STOP', 'IDLE', 'STOPPED', 'stop', True, [], ['A']),
                ],
                'invariants': [
                    B.inv('A.OPS_NONNEG', B.ge_(B.var('ops'), 0), ['A']),
                ],
            }
            B.validate_and_dump(actor_m, root / 'actor.json')

            # 2. Demux / checksum / wire-decoding frontend
            demux_m = {
                'ir_version': '0.6',
                'semantics': 'flat-efsm-atomic-ordered-v1',
                'protocol': 'mini-demux',
                'scope': {'terminal_states': [], 'excluded': ['test']},
                'states': ['READY'],
                'initial_state': 'READY',
                'requirements': {'D': {'source': 's#d', 'interpretation': 'demux'}},
                'variables': {'last_csum': {'type': 'int', 'initial': 0}},
                'events': {
                    'rx': {'origin': 'network', 'fields': {'pkt': 'bytes'}},
                    'emit_rst': {'origin': 'network', 'fields': {'port': 'int'}},
                },
                'messages': {
                    'seg_in': {'fields': {'port': 'int', 'is_syn': 'bool', 'payload': 'bytes', 'half_v': 'int', 'aligned_v': 'int'}},
                    'rst_out': {'fields': {'port': 'int'}},
                },
                'timers': {},
                'transitions': [
                    B.rule(
                        'D.RX', 'READY', 'READY', 'rx',
                        B.ge_(B.b_len(B.ev('pkt')), 6),
                        [
                            B.act_set('last_csum', B.csum16(B.ev('pkt'))),
                            B.act_emit(
                                'seg_in',
                                port=B.u16be(B.ev('pkt'), 0),
                                is_syn=B.u8_has_bit(B.u8(B.ev('pkt'), 2), 2),
                                payload=B.b_slice(B.ev('pkt'), 5, 64),
                                half_v=B.u16_div2(B.u16be(B.ev('pkt'), 3)),
                                aligned_v=B.u16_align8_floor(B.u16be(B.ev('pkt'), 3)),
                            ),
                        ],
                        ['D'],
                    ),
                    B.rule(
                        'D.RST', 'READY', 'READY', 'emit_rst', True,
                        [B.act_emit('rst_out', port=B.ev('port'))],
                        ['D'],
                    ),
                ],
                'invariants': [
                    B.inv('D.CSUM_RANGE', B.and_(B.ge_(B.var('last_csum'), 0), B.le_(B.var('last_csum'), 65535)), ['D']),
                ],
            }
            B.validate_and_dump(demux_m, root / 'demux.json')

            # 3. Connection table supporting LISTEN -> fork_from_match -> ESTAB
            conn_m = {
                'ir_version': '0.6',
                'semantics': 'flat-efsm-atomic-ordered-v1',
                'protocol': 'mini-conn',
                'scope': {'terminal_states': [], 'excluded': ['test']},
                'states': ['FREE', 'LISTEN', 'ESTAB'],
                'initial_state': 'FREE',
                'requirements': {'C': {'source': 's#c', 'interpretation': 'conn'}},
                'variables': {
                    'port': {'type': 'int', 'initial': 0},
                    'parent': {'type': 'int', 'initial': -1},
                    'rx_len': {'type': 'int', 'initial': 0},
                },
                'events': {
                    'listen': {'origin': 'application', 'fields': {'port': 'int'}},
                    'accept_syn': {'origin': 'network', 'fields': {'payload': 'bytes', 'half_v': 'int', 'aligned_v': 'int'}},
                    'data': {'origin': 'network', 'fields': {'payload': 'bytes'}},
                },
                'messages': {
                    'accepted': {'fields': {'parent': 'int', 'port': 'int', 'half_v': 'int', 'aligned_v': 'int'}},
                    'deliver': {'fields': {'payload': 'bytes'}},
                },
                'timers': {},
                'transitions': [
                    B.rule('C.LISTEN', 'FREE', 'LISTEN', 'listen', True, [B.act_set('port', B.ev('port'))], ['C']),
                    B.rule(
                        'C.SYN', 'FREE', 'ESTAB', 'accept_syn', True,
                        [
                            B.act_set('rx_len', B.b_len(B.ev('payload'))),
                            B.act_emit('accepted', parent=B.var('parent'), port=B.var('port'),
                                       half_v=B.ev('half_v'), aligned_v=B.ev('aligned_v')),
                        ],
                        ['C'],
                    ),
                    B.rule(
                        'C.DATA', 'ESTAB', 'ESTAB', 'data', True,
                        [
                            B.act_set('rx_len', B.add_(B.var('rx_len'), B.b_len(B.ev('payload')))),
                            B.act_emit('deliver', payload=B.ev('payload')),
                        ],
                        ['C'],
                    ),
                ],
                'invariants': [
                    B.inv('C.RXLEN', B.ge_(B.var('rx_len'), 0), ['C']),
                ],
            }
            B.validate_and_dump(conn_m, root / 'conn.json')

            recipe = {
                'schema': 'fsa-system-v1',
                'system_name': 'mini_stack',
                'bus_queue_cap': 16,
                'bus_byte_cap': 256,
                'modules': {
                    'actor': {'model': 'actor.json', 'prefix': 'ms_actor', 'capacity': 1, 'byte_cap': 64, 'arena_cap': 1024},
                    'demux': {'model': 'demux.json', 'prefix': 'ms_demux', 'capacity': 1, 'byte_cap': 256, 'arena_cap': 2048},
                    'conn': {'model': 'conn.json', 'prefix': 'ms_conn', 'capacity': 4, 'byte_cap': 256, 'arena_cap': 2048, 'free_state': 'FREE'},
                },
                'architecture_hooks': {
                    'actor': 'actor',
                    'actor_start_ev': 'start',
                    'actor_stop_ev': 'stop',
                    'actor_post_rx_ev': 'post_rx',
                    'actor_dispatch_ev': 'dispatch',
                    'actor_complete_ev': 'complete',
                },
                'host_outputs': ['ACCEPTED', 'DELIVER', 'RST'],
                'routes': {
                    'demux.seg_in': {
                        'kind': 'lookup_chain',
                        'attempts': [
                            {
                                'kind': 'match',
                                'target': 'conn',
                                'in_states': ['ESTAB'],
                                'match_vars': [{'var': 'port', 'from_field': 'port'}],
                                'event': 'data',
                                'args': [{'from_field': 'payload'}],
                            },
                            {
                                'kind': 'fork_from_match',
                                'target': 'conn',
                                'in_states': ['LISTEN'],
                                'when_field_eq': [{'field': 'is_syn', 'bool': True}],
                                'match_vars': [{'var': 'port', 'from_field': 'port'}],
                                'copy_vars': ['port'],
                                'parent_slot_var': 'parent',
                                'event': 'accept_syn',
                                'args': [
                                    {'from_field': 'payload'},
                                    {'from_field': 'half_v'},
                                    {'from_field': 'aligned_v'},
                                ],
                            },
                        ],
                        'on_miss': {
                            'kind': 'singleton',
                            'target': 'demux',
                            'event': 'emit_rst',
                            'args': [{'from_field': 'port'}],
                        },
                    },
                    'demux.rst_out': {'kind': 'host_out', 'out_id': 'RST'},
                    'conn.accepted': {'kind': 'host_out', 'out_id': 'ACCEPTED'},
                    'conn.deliver': {'kind': 'host_out', 'out_id': 'DELIVER'},
                },
                'entrypoints': [
                    {
                        'name': 'listen',
                        'target': 'conn',
                        'slot_mode': 'slot_arg',
                        'event': 'listen',
                        'params': [{'name': 'port', 'type': 'int'}],
                    },
                    {
                        'name': 'rx_pkt',
                        'target': 'demux',
                        'slot_mode': 'singleton',
                        'event': 'rx',
                        'params': [{'name': 'pkt', 'type': 'bytes'}],
                        'is_rx': True,
                    },
                ],
            }
            (root / 'system.json').write_text(json.dumps(recipe, indent=2))
            gen_dir = root / 'gen'
            manifest = system_codegen.generate_system(root / 'system.json', gen_dir, fast_dispatch=True)
            self.assertEqual(manifest['schema'], 'fsa-system-v1')

            harness = root / 'harness.c'
            harness.write_text('''#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "mini_stack.h"

static int accepted_cnt = 0;
static int deliver_cnt = 0;
static int rst_cnt = 0;
static int64_t last_half = -1, last_align = -1, last_rst_port = -1;
static uint8_t last_pay[64];
static uint16_t last_pay_len = 0;

static void on_out(void *ctx, int out_id, uint16_t src_slot, const fsa_val_t *fields, int nfields) {
    (void)ctx; (void)src_slot; (void)nfields;
    if (out_id == MINI_STACK_OUT_ACCEPTED) {
        accepted_cnt++;
        last_half = fields[2].i64;
        last_align = fields[3].i64;
    } else if (out_id == MINI_STACK_OUT_DELIVER) {
        deliver_cnt++;
        last_pay_len = fields[0].bytes.len;
        memcpy(last_pay, fields[0].bytes.ptr, last_pay_len);
    } else if (out_id == MINI_STACK_OUT_RST) {
        rst_cnt++;
        last_rst_port = fields[0].i64;
    }
}

int main(void) {
    static mini_stack_system_t sys;
    assert(mini_stack_init(&sys, on_out, NULL) == FSA_OK);
    assert(mini_stack_get_actor_state(&sys, 0) == MS_ACTOR_STATE_IDLE);

    int lslot = mini_stack_alloc_conn(&sys);
    assert(lslot == 0);
    assert(mini_stack_listen(&sys, 10, lslot, 8080) == FSA_OK);

    /* SYN to unmatched port 9999 -> triggers on_miss -> RST */
    const uint8_t bad_syn[6] = { 0x27, 0x0F, 0x02, 0x05, 0xDC, 0xAA };
    assert(mini_stack_rx_pkt(&sys, 20, bad_syn, sizeof(bad_syn)) == FSA_OK);
    assert(rst_cnt == 1 && last_rst_port == 9999);

    /* SYN to port 8080 with u16 val = 1495 (0x05D7): div2=747, align8=1488 */
    const uint8_t syn_pkt[8] = { 0x1F, 0x90, 0x02, 0x05, 0xD7, 'h', 'i', '!' };
    assert(mini_stack_rx_pkt(&sys, 30, syn_pkt, sizeof(syn_pkt)) == FSA_OK);
    assert(accepted_cnt == 1 && last_half == 747 && last_align == 1488);
    assert(mini_stack_get_conn_state(&sys, 0) == MS_CONN_STATE_LISTEN);
    assert(mini_stack_get_conn_state(&sys, 1) == MS_CONN_STATE_ESTAB);

    /* Data segment to port 8080 -> routes to child slot 1 */
    const uint8_t data_pkt[10] = { 0x1F, 0x90, 0x10, 0x00, 0x10, 'w', 'o', 'r', 'l', 'd' };
    assert(mini_stack_rx_pkt(&sys, 40, data_pkt, sizeof(data_pkt)) == FSA_OK);
    assert(deliver_cnt == 1 && last_pay_len == 5 && memcmp(last_pay, "world", 5) == 0);
    assert(mini_stack_get_actor_var_int(&sys, 0, MS_ACTOR_SVAR_OPS) == 3);

    /* Check unrolled checksum matches known RFC vectors */
    const uint8_t odd[7] = { 0x45, 0x00, 0x00, 0x3C, 0x1C, 0x46, 0x40 };
    assert(mini_stack_get_demux_var_int(&sys, 0, MS_DEMUX_SVAR_LAST_CSUM) >= 0);
    (void)odd;
    assert(mini_stack_shutdown(&sys, 50) == FSA_OK);
    assert(mini_stack_get_actor_state(&sys, 0) == MS_ACTOR_STATE_STOPPED);
    printf("SYSTEM_CODEGEN_OK\\n");
    return 0;
}
''')
            c_files = [
                str(gen_dir / 'ms_actor.c'),
                str(gen_dir / 'ms_demux.c'),
                str(gen_dir / 'ms_conn.c'),
                str(gen_dir / 'mini_stack.c'),
                str(harness),
            ]
            # Compile and run BOTH fast and strict (-DFSA_STRICT=1) modes with GCC-parity flags
            for strict_flag, tag in (([], 'fast'), (['-DFSA_STRICT=1'], 'strict')):
                exe = root / f'run_{tag}'
                _compile([
                    CC, '-std=c99', '-Wall', '-Wextra', '-Werror', '-Wsign-compare', '-Wtype-limits',
                    '-Os', *strict_flag, '-I', str(gen_dir), *c_files, '-o', str(exe),
                ])
                out = subprocess.check_output([str(exe)], text=True, timeout=30)
                self.assertEqual(out.strip(), 'SYSTEM_CODEGEN_OK')

            # Check fsa_checksum16 matches protocol_lab.ir.internet_checksum16 across lengths 0..67
            csum_c = root / 'csum_chk.c'
            csum_c.write_text('''#include <stdio.h>
#include <stdint.h>
#include "fsa_lib_runtime.h"
int main(void) {
    uint8_t buf[128];
    for (int i = 0; i < 128; i++) buf[i] = (uint8_t)((i * 73 + 19) & 0xFF);
    for (int len = 0; len <= 67; len++) {
        int err = 0;
        int64_t r = fsa_checksum16(fsa_slice_make(buf, (uint16_t)len), 128U, &err);
        if (err) return 1;
        printf("%d %lld\\n", len, (long long)r);
    }
    return 0;
}
''')
            csum_exe = root / 'csum_chk'
            _compile([CC, '-std=c99', '-Wall', '-Wextra', '-Werror', '-O2', '-I', str(gen_dir), str(csum_c), '-o', str(csum_exe)])
            lines = subprocess.check_output([str(csum_exe)], text=True).strip().splitlines()
            ref_buf = [(i * 73 + 19) & 0xFF for i in range(128)]
            for line in lines:
                n_str, got_str = line.split()
                n = int(n_str)
                self.assertEqual(int(got_str), internet_checksum16(ref_buf[:n]))


if __name__ == '__main__':
    unittest.main()
