"""Tests, differential equivalence, size, and throughput checks for `c99-lib-v1`."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from formal_spec_agent import codegen_lib
from protocol_lab.ir import load

ROOT = Path(__file__).resolve().parents[1]
EXAMPLES = ROOT / 'examples'
TCPIP_ROOT = Path(os.environ.get('FSA_TCPIP_REGRESSION_DIR', str(ROOT.parent / 'TCPIP-Model')))
CC = shutil.which('cc')


def _compile(cmd):
    res = subprocess.run(cmd, capture_output=True, text=True, timeout=120)
    if res.returncode != 0:
        raise AssertionError(f'Command failed {cmd}:\n{res.stdout}\n{res.stderr}')
    return res


def _text_size(obj_path: Path):
    sz = shutil.which('size')
    if not sz:
        return None
    out = subprocess.check_output([sz, str(obj_path)], text=True)
    lines = [l.strip() for l in out.splitlines() if l.strip()]
    if len(lines) >= 2:
        parts = lines[1].split()
        if parts and parts[0].isdigit():
            return int(parts[0])
    return None


@unittest.skipUnless(CC, 'C99 compiler named cc required')
class CodegenLibTests(unittest.TestCase):
    def test_scalar_only_fsm_compiles_with_no_heap_or_stdio_and_zero_warnings(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            model_path = root / 'scalar.json'
            model_path.write_text(json.dumps({
                'ir_version': '0.6',
                'semantics': 'flat-efsm-atomic-ordered-v1',
                'protocol': 'scalar-lock',
                'scope': {'terminal_states': [], 'excluded': ['toy']},
                'states': ['FREE', 'HELD'],
                'initial_state': 'FREE',
                'requirements': {'LOCK': {'source': 's.md#lock', 'interpretation': 'mutex'}},
                'variables': {'owner': {'type': 'int', 'initial': -1}, 'count': {'type': 'int', 'initial': 0}},
                'events': {
                    'acquire': {'origin': 'application', 'fields': {'tid': 'int'}},
                    'release': {'origin': 'application', 'fields': {'tid': 'int'}},
                },
                'messages': {'grant': {'fields': {'tid': 'int'}}},
                'timers': {},
                'transitions': [
                    {
                        'id': 'LOCK.ACQUIRE', 'from': 'FREE', 'to': 'HELD', 'event': 'acquire',
                        'guard': {'op': 'ge', 'args': [{'event': 'tid'}, 0]},
                        'actions': [
                            {'set': {'var': 'owner', 'value': {'event': 'tid'}}},
                            {'set': {'var': 'count', 'value': 1}},
                            {'emit': {'message': 'grant', 'fields': {'tid': {'var': 'owner'}}}},
                        ],
                        'requirements': ['LOCK'],
                    },
                    {
                        'id': 'LOCK.RELEASE', 'from': 'HELD', 'to': 'FREE', 'event': 'release',
                        'guard': {'op': 'eq', 'args': [{'event': 'tid'}, {'var': 'owner'}]},
                        'actions': [
                            {'set': {'var': 'owner', 'value': -1}},
                            {'set': {'var': 'count', 'value': 0}},
                        ],
                        'requirements': ['LOCK'],
                    },
                ],
                'invariants': [
                    {'id': 'VALID_COUNT', 'assert': {'op': 'ge', 'args': [{'var': 'count'}, 0]}, 'requirements': ['LOCK']},
                ],
            }))

            lib_dir = root / 'lib'
            meta = codegen_lib.generate_lib(model_path, lib_dir, prefix='slock', fast_dispatch=True)
            self.assertEqual(meta['backend'], 'c99-lib-v1')
            self.assertEqual(meta['byte_vars'], 0)
            self.assertEqual(meta['timers'], 0)
            hdr = (lib_dir / 'slock.h').read_text()
            self.assertNotIn('bdata', hdr)

            obj = root / 'slock.o'
            _compile([CC, '-std=c99', '-Wall', '-Wextra', '-Werror', '-Os', '-c', str(lib_dir / 'slock.c'), '-o', str(obj)])
            nm = shutil.which('nm')
            if nm:
                undef = subprocess.check_output([nm, '-u', str(obj)], text=True)
                for bad in ('printf', 'malloc', 'free', 'calloc', 'fopen', 'snprintf'):
                    self.assertNotIn(bad, undef)

            driver = root / 'drv.c'
            driver.write_text('''
#include <assert.h>
#include "slock.h"
static int granted_tid = -999;
static void on_emit(void *ctx, int msg_id, const fsa_val_t *fields, int nfields) {
    (void)ctx;
    assert(msg_id == SLOCK_MSG_GRANT && nfields == 1);
    granted_tid = (int)fields[0].i64;
}
int main(void) {
    slock_machine_t m;
    assert(slock_init(&m) == FSA_OK);
    assert(slock_next_due_ms(&m) == -1);
    fsa_val_t a1[1] = { fsa_val_int(7) };
    int rule = -1;
    assert(slock_step(&m, 10, SLOCK_EV_ACQUIRE, a1, 1, on_emit, NULL, &rule) == FSA_OK);
    assert(granted_tid == 7 && m.state == SLOCK_STATE_HELD && rule == 0);
    fsa_val_t bad[1] = { fsa_val_int(8) };
    assert(slock_step(&m, 11, SLOCK_EV_RELEASE, bad, 1, on_emit, NULL, &rule) == -FSA_ERR_UNCOVERED);
    assert(m.state == SLOCK_STATE_HELD);
    assert(slock_step(&m, 12, SLOCK_EV_RELEASE, a1, 1, on_emit, NULL, &rule) == FSA_OK);
    assert(m.state == SLOCK_STATE_FREE && m.v[SLOCK_SVAR_OWNER] == -1);
    return 0;
}
''')
            exe = root / 'drv'
            _compile([CC, '-std=c99', '-Wall', '-Wextra', '-Werror', '-Os', '-I', str(lib_dir), str(driver), str(obj), '-o', str(exe)])
            _compile([str(exe)])

    def test_empty_events_and_zero_transitions_compile_zero_warnings(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            mpath = root / 'empty.json'
            mpath.write_text(json.dumps({
                'ir_version': '0.6',
                'semantics': 'flat-efsm-atomic-ordered-v1',
                'protocol': 'empty-fsm',
                'scope': {'terminal_states': [], 'excluded': ['empty']},
                'states': ['IDLE'],
                'initial_state': 'IDLE',
                'requirements': {'R': {'source': 's.md#r', 'interpretation': 'empty'}},
                'variables': {'x': {'type': 'int', 'initial': 0}},
                'events': {},
                'messages': {},
                'timers': {},
                'transitions': [],
                'invariants': [{'id': 'Z', 'assert': {'op': 'eq', 'args': [{'var': 'x'}, 0]}, 'requirements': ['R']}],
            }))
            out_lib = root / 'empty_lib'
            codegen_lib.generate_lib(mpath, out_lib, prefix='efsm', fast_dispatch=True)
            _compile([CC, '-std=c99', '-Wall', '-Wextra', '-Werror', '-Os', '-c', str(out_lib / 'efsm.c'), '-o', str(root / 'efsm.o')])

    def test_emit_overflow_still_fails_when_on_emit_is_null(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            mpath = root / 'emit_err.json'
            mpath.write_text(json.dumps({
                'ir_version': '0.6',
                'semantics': 'flat-efsm-atomic-ordered-v1',
                'protocol': 'emit-err',
                'scope': {'terminal_states': [], 'excluded': ['ovf']},
                'states': ['S0'],
                'initial_state': 'S0',
                'requirements': {'R': {'source': 's.md#r', 'interpretation': 'ovf'}},
                'variables': {'x': {'type': 'int', 'initial': (1 << 62)}},
                'events': {'go': {'origin': 'application', 'fields': {'d': 'int'}}},
                'messages': {'out': {'fields': {'v': 'int'}}},
                'timers': {},
                'transitions': [{
                    'id': 'R0', 'from': 'S0', 'to': 'S0', 'event': 'go', 'guard': True,
                    'actions': [{'emit': {'message': 'out', 'fields': {'v': {'op': 'add', 'args': [{'var': 'x'}, {'event': 'd'}]}}}}],
                    'requirements': ['R'],
                }],
                'invariants': [],
            }))
            out_lib = root / 'ovf_lib'
            codegen_lib.generate_lib(mpath, out_lib, prefix='ovf', fast_dispatch=False)
            drv = root / 'drv.c'
            drv.write_text('''
#include <assert.h>
#include "ovf.h"
int main(void) {
    ovf_machine_t m;
    assert(ovf_init(&m) == FSA_OK);
    fsa_val_t ok_arg[1] = { fsa_val_int(1) };
    assert(ovf_step(&m, 1, OVF_EV_GO, ok_arg, 1, NULL, NULL, NULL) == FSA_OK);
    fsa_val_t bad_arg[1] = { fsa_val_int(INT64_MAX) };
    assert(ovf_step(&m, 2, OVF_EV_GO, bad_arg, 1, NULL, NULL, NULL) == -FSA_ERR_OVERFLOW);
    return 0;
}
''')
            exe = root / 'ovf_drv'
            _compile([CC, '-std=c99', '-Wall', '-Wextra', '-Werror', '-Os', '-I', str(out_lib), str(drv), str(out_lib / 'ovf.c'), '-o', str(exe)])
            _compile([str(exe)])

    def test_timed_dynamic_text_efsm_timers_and_atomic_rollback(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            lib_dir = root / 'tcell'
            meta = codegen_lib.generate_lib(
                EXAMPLES / 'lean-timed-efsm/model.json', lib_dir, prefix='tcell', byte_cap=256, debug_names=True
            )
            self.assertTrue(meta['has_text_events'])
            self.assertEqual(meta['timers'], 1)
            driver = root / 'test_tcell.c'
            driver.write_text('''
#include <assert.h>
#include <string.h>
#include "tcell.h"

static int last_msg = -1;
static char last_label[64];
static uint8_t last_buf[64];
static uint16_t last_blen = 0;

static void on_emit(void *ctx, int msg_id, const fsa_val_t *fields, int nfields) {
    (void)ctx;
    last_msg = msg_id;
    assert(nfields == 5);
    last_blen = fields[0].bytes.len;
    if (last_blen) memcpy(last_buf, fields[0].bytes.ptr, last_blen);
    memset(last_label, 0, sizeof(last_label));
    if (fields[3].bytes.len) memcpy(last_label, fields[3].bytes.ptr, fields[3].bytes.len);
}

int main(void) {
    tcell_machine_t m;
    assert(tcell_init(&m) == FSA_OK);
    assert(strcmp(tcell_state_name(m.state), "COLD") == 0);

    const uint8_t payload[3] = {1, 2, 3};
    fsa_val_t args[5] = {
        fsa_val_bytes(payload, 3),
        fsa_val_seq32(100),
        fsa_val_int(5),
        fsa_val_str("hi", 2),
        fsa_val_bool(1)
    };
    int rule = -1;
    assert(tcell_step(&m, 100, TCELL_EV_APP_PUT, args, 5, on_emit, NULL, &rule) == FSA_OK);
    assert(m.state == TCELL_STATE_HOT);
    assert(last_msg == TCELL_MSG_CELL_ACCEPT && last_blen == 3 && strcmp(last_label, "hi") == 0);
    assert(tcell_next_due_ms(&m) == 110);

    /* Invalid UTF-8 rolls back without firing or mutating state/pool */
    const char bad_utf8[2] = { (char)0xFF, (char)0x80 };
    args[3] = fsa_val_str(bad_utf8, 2);
    int prev_pool = m.texts.count;
    assert(tcell_step(&m, 105, TCELL_EV_APP_PUT, args, 5, on_emit, NULL, &rule) < 0);
    assert(m.texts.count == prev_pool && m.now_ms == 100 && m.state == TCELL_STATE_HOT);

    /* Advance past expiry fires timer.expiry */
    assert(tcell_tick(&m, 115, on_emit, NULL) == FSA_OK);
    assert(m.state == TCELL_STATE_COLD && last_msg == TCELL_MSG_CELL_EXPIRED && tcell_next_due_ms(&m) == -1);
    return 0;
}
''')
            exe = root / 'test_tcell'
            _compile([
                CC, '-std=c99', '-Wall', '-Wextra', '-Werror', '-Os', '-I', str(lib_dir),
                str(driver), str(lib_dir / 'tcell.c'), '-o', str(exe),
            ])
            _compile([str(exe)])

    def test_tcpip_regression_24_paths_157_transitions_exact_match_and_benchmark(self):
        model_path = TCPIP_ROOT / 'model/ipv4-endpoint-virtual-link.json'
        reg_path = TCPIP_ROOT / 'tests/optimization-regression.json'
        if not (model_path.is_file() and reg_path.is_file()):
            self.skipTest('Sibling TCPIP-Model regression files unavailable')

        reg = json.loads(reg_path.read_text())
        model = load(model_path)
        scalar_vars = [n for n, v in model['variables'].items() if v['type'] != 'bytes']
        byte_vars = [n for n, v in model['variables'].items() if v['type'] == 'bytes']
        events = list(model['events'])
        messages = list(model['messages'])
        states = model['states']
        rules = [r['id'] for r in model['transitions']]

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            strict_dir = root / 'lib_strict'
            fast_dir = root / 'lib_fast'
            meta_s = codegen_lib.generate_lib(model_path, strict_dir, prefix='tcpip', byte_cap=2048, debug_names=True)
            meta_f = codegen_lib.generate_lib(
                model_path, fast_dir, prefix='tcpip', byte_cap=2048, fast_dispatch=True, debug_names=False
            )
            self.assertGreater(meta_s['decision_tree_switches'], 0)

            obj_s = root / 'tcpip_strict.o'
            obj_f = root / 'tcpip_fast.o'
            _compile([CC, '-std=c99', '-Wall', '-Wextra', '-Werror', '-Os', '-ffunction-sections', '-c',
                      str(strict_dir / 'tcpip.c'), '-o', str(obj_s)])
            _compile([CC, '-std=c99', '-Wall', '-Wextra', '-Werror', '-Os', '-ffunction-sections', '-c',
                      str(fast_dir / 'tcpip.c'), '-o', str(obj_f)])

            # Build native runner wrapper that executes traced command scripts using tcpip_step() and outputs JSON per transition
            harness_c = root / 'diff_harness.c'
            harness_c.write_text('''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "tcpip.h"

typedef struct {
    int count;
} emit_ctx_t;

static void print_row_header(int rc, int rule, const tcpip_machine_t *m) {
    printf("],\\"rc\\":%d,\\"rule\\":\\"%s\\",\\"state\\":\\"%s\\",\\"scalars\\":[",
           rc, rule >= 0 ? tcpip_rule_name(rule) : "", tcpip_state_name(m->state));
    for (int i = 0; i < TCPIP_NUM_SCALAR_VARS; i++) printf("%s%lld", i ? "," : "", (long long)m->v[i]);
    printf("],\\"strings\\":[");
    for (int i = 0; i < TCPIP_NUM_SCALAR_VARS; i++) printf("%s\\"%s\\"", i ? "," : "", tcpip_string_literal(m->v[i]));
    printf("]}\\n");
}

static int hex_nib(char c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    if (c >= 'A' && c <= 'F') return c - 'A' + 10;
    return -1;
}

static size_t parse_hex(const char *s, uint8_t *out, size_t cap) {
    if (s[0] != 'b' || s[1] != ':') abort();
    size_t n = strlen(s + 2) / 2;
    if (n > cap) abort();
    for (size_t i = 0; i < n; i++) {
        out[i] = (uint8_t)((hex_nib(s[2 + 2*i]) << 4) | hex_nib(s[3 + 2*i]));
    }
    return n;
}

static void on_emit(void *vctx, int msg_id, const fsa_val_t *fields, int nfields) {
    emit_ctx_t *ctx = (emit_ctx_t *)vctx;
    printf("%s", ctx->count++ ? "," : "");
    printf("{\\"message\\":\\"%s\\",\\"fields\\":[", tcpip_msg_name(msg_id));
    for (int i = 0; i < nfields; i++) {
        if (i) printf(",");
        if (fields[i].kind == FSA_KIND_BYTES) {
            printf("\\"");
            for (uint16_t j = 0; j < fields[i].bytes.len; j++) printf("%02x", fields[i].bytes.ptr[j]);
            printf("\\"");
        } else if (fields[i].kind == FSA_KIND_STRING) {
            printf("\\"%s\\"", (const char *)fields[i].bytes.ptr);
        } else {
            printf("%lld", (long long)fields[i].i64);
        }
    }
    printf("]}");
}

static void drain_timers(tcpip_machine_t *m, int64_t at) {
    for (;;) {
        int64_t due = tcpip_next_due_ms(m);
        if (due < 0 || due > at) break;
        int rule = -1;
        emit_ctx_t ec = {0};
        printf("{\\"emitted\\":[");
        int trc = tcpip_tick_one(m, at, on_emit, &ec, &rule);
        print_row_header(trc > 0 ? 0 : trc, rule, m);
        if (trc <= 0) break;
    }
    if (tcpip_tick(m, at, NULL, NULL) != FSA_OK) abort();
}

int main(int argc, char **argv) {
    if (argc > 1 && strcmp(argv[1], "--bench") == 0) {
        int iters = atoi(argv[2]);
        tcpip_machine_t m;
        uint8_t pkt[60] = {2,0,0,0,0,1, 2,0,0,0,0,2, 8,0, 0x45,0,0,28,0,0,0x40,0,64,1,0xf7,0x8c,192,0,2,2,192,0,2,1, 8,0,0xf7,0xfc,0,1,0,1};
        (void)pkt;
        tcpip_init(&m);
        /* Resolve ARP once then pump ECHO requests */
        uint8_t arp_rep[60] = {2,0,0,0,0,1,2,0,0,0,0,2,8,6,0,1,8,0,6,4,0,2,2,0,0,0,0,2,192,0,2,2,2,0,0,0,0,1,192,0,2,1};
        uint8_t resolve_ip[4] = {192,0,2,2};
        fsa_val_t rargs[1] = { fsa_val_bytes(resolve_ip, 4) };
        fsa_val_t aargs[1] = { fsa_val_bytes(arp_rep, 60) };
        int rule = -1;
        if (tcpip_step(&m, 0, TCPIP_EV_L_APP_RESOLVE, rargs, 1, NULL, NULL, &rule) != FSA_OK) return 2;
        if (tcpip_step(&m, 1, TCPIP_EV_L_NET_FRAME, aargs, 1, NULL, NULL, &rule) != FSA_OK) return 3;
        /* Build valid IPv4 ICMP Echo Request checksum: cksum ip + icmp */
        uint32_t sum = 0;
        for (int i = 14; i < 34; i += 2) sum += ((uint32_t)pkt[i] << 8) | pkt[i+1];
        /* recompute IP header csum dynamically */
        pkt[24] = pkt[25] = 0;
        sum = 0;
        for (int i = 14; i < 34; i += 2) sum += ((uint32_t)pkt[i] << 8) | pkt[i+1];
        while (sum >> 16) sum = (sum & 0xFFFFU) + (sum >> 16);
        uint16_t ics = (uint16_t)(0xFFFFU - sum);
        pkt[24] = (uint8_t)(ics >> 8); pkt[25] = (uint8_t)(ics & 0xFF);
        pkt[36] = pkt[37] = 0;
        sum = 0;
        for (int i = 34; i < 42; i += 2) sum += ((uint32_t)pkt[i] << 8) | pkt[i+1];
        while (sum >> 16) sum = (sum & 0xFFFFU) + (sum >> 16);
        uint16_t cks = (uint16_t)(0xFFFFU - sum);
        pkt[36] = (uint8_t)(cks >> 8); pkt[37] = (uint8_t)(cks & 0xFF);
        fsa_val_t eargs[1] = { fsa_val_bytes(pkt, 60) };
        for (int i = 0; i < iters; i++) {
            int rc = tcpip_step(&m, 2 + i, TCPIP_EV_L_NET_FRAME, eargs, 1, NULL, NULL, &rule);
            if (rc != FSA_OK) return 4;
        }
        return 0;
    }

    tcpip_machine_t m;
    tcpip_init(&m);
    char line[8192];
    static uint8_t bbufs[8][2048];
    while (fgets(line, sizeof(line), stdin)) {
        char *tok = strtok(line, " \\t\\r\\n");
        if (!tok) continue;
        if (strcmp(tok, "B") == 0) continue;
        if (strcmp(tok, "T") == 0) {
            int64_t at = strtoll(strtok(NULL, " \\t\\r\\n"), NULL, 10);
            drain_timers(&m, at);
            continue;
        }
        if (strcmp(tok, "D") == 0) {
            int64_t at = strtoll(strtok(NULL, " \\t\\r\\n"), NULL, 10);
            drain_timers(&m, at);
            char *evname = strtok(NULL, " \\t\\r\\n");
            int ev = -1;
            for (int i = 0; i < TCPIP_NUM_EVENTS; i++) {
                if (strcmp(evname, tcpip_event_name(i)) == 0) { ev = i; break; }
            }
            fsa_val_t args[8];
            int nargs = 0;
            char *arg;
            while ((arg = strtok(NULL, " \\t\\r\\n")) != NULL) {
                if (arg[0] == 'b' && arg[1] == ':') {
                    size_t n = parse_hex(arg, bbufs[nargs], 2048);
                    args[nargs] = fsa_val_bytes(bbufs[nargs], (uint16_t)n);
                } else if (strcmp(arg, "true") == 0 || strcmp(arg, "false") == 0) {
                    args[nargs] = fsa_val_bool(strcmp(arg, "true") == 0);
                } else {
                    /* Note: tests encode seq32 & int as integers, distinguish below if needed */
                    args[nargs] = fsa_val_int(strtoll(arg, NULL, 10));
                }
                nargs++;
            }
            /* Fix up bool/seq32 kind tags based on model metadata when needed */
            if (strcmp(evname, "L.app.configure_checksum") == 0 || strcmp(evname, "L.app.require_checksum") == 0) {
                args[0].kind = FSA_KIND_BOOL;
            } else if (strcmp(evname, "T.net.syn") == 0 || strcmp(evname, "T.net.rst") == 0) {
                args[0].kind = FSA_KIND_SEQ32;
            } else if (strcmp(evname, "T.net.synack") == 0 || strcmp(evname, "T.net.ack") == 0 ||
                       strcmp(evname, "T.net.fin") == 0 || strcmp(evname, "T.net.rstack") == 0 ||
                       strcmp(evname, "T.net.data") == 0) {
                args[0].kind = FSA_KIND_SEQ32;
                args[1].kind = FSA_KIND_SEQ32;
            }
            int rule = -1;
            emit_ctx_t ec = {0};
            printf("{\\"emitted\\":[");
            int rc = tcpip_step(&m, at, ev, args, nargs, on_emit, &ec, &rule);
            print_row_header(rc, rule, &m);
        }
    }
    return 0;
}
''')
            diff_exe = root / 'diff_harness'
            _compile([
                CC, '-std=c99', '-Wall', '-Wextra', '-Werror', '-O2', '-I', str(strict_dir),
                str(harness_c), str(obj_s), '-o', str(diff_exe),
            ])

            # Compile the original v6 baseline C for direct differential comparison
            v6_c = TCPIP_ROOT / 'code/generated/protocol.c'
            v6_obj = root / 'v6.o'
            v6_exe = root / 'v6_exe'
            _compile([CC, '-std=c99', '-Wall', '-Wextra', '-Werror', '-Os', '-c', str(v6_c), '-o', str(v6_obj)])
            _compile([CC, '-std=c99', '-Wall', '-Wextra', '-Werror', '-O2', str(v6_c), '-o', str(v6_exe)])

            total_transitions = 0
            for case in reg['cases']:
                # Run v6 executable
                v6_out = subprocess.run([str(v6_exe)], input=case['input'], capture_output=True, text=True, timeout=30)
                self.assertEqual(v6_out.returncode, case['returncode'])
                v6_trans = [json.loads(l) for l in v6_out.stdout.splitlines() if json.loads(l).get('status') == 'transition']

                # Run c99-lib-v1 harness
                lib_out = subprocess.run([str(diff_exe)], input=case['input'], capture_output=True, text=True, timeout=30)
                self.assertEqual(lib_out.returncode, 0)
                lib_rows = [json.loads(l) for l in lib_out.stdout.splitlines()]
                self.assertEqual(len(lib_rows), len(v6_trans), case['id'])

                for idx, (vr, lr) in enumerate(zip(v6_trans, lib_rows)):
                    self.assertEqual(lr['rc'], 0, f"{case['id']} step {idx}")
                    self.assertEqual(lr['rule'], vr['transition'], f"{case['id']} step {idx}")
                    self.assertEqual(lr['state'], vr['after']['state'], f"{case['id']} step {idx}")
                    # Verify scalar variables match
                    after_vars = vr['after']['variables']
                    for si, vname in enumerate(scalar_vars):
                        vspec = model['variables'][vname]
                        expected_v = after_vars[vname]
                        if vspec['type'] == 'string':
                            self.assertEqual(lr['strings'][si], expected_v, f"{case['id']} var {vname}")
                        elif vspec['type'] == 'bool':
                            self.assertEqual(bool(lr['scalars'][si]), expected_v, f"{case['id']} var {vname}")
                        else:
                            self.assertEqual(lr['scalars'][si], expected_v, f"{case['id']} var {vname}")
                    # Verify emitted messages & byte payloads match
                    expected_emits = vr['emitted']
                    self.assertEqual(len(lr['emitted']), len(expected_emits), f"{case['id']} step {idx} emits")
                    for le, ve in zip(lr['emitted'], expected_emits):
                        self.assertEqual(le['message'], ve['message'])
                        mfields = model['messages'][ve['message']]['fields']
                        for fi, (fn, fk) in enumerate(mfields.items()):
                            if fk == 'bytes':
                                self.assertEqual(le['fields'][fi], bytes(ve['fields'][fn]).hex())
                            elif fk == 'bool':
                                self.assertEqual(bool(le['fields'][fi]), ve['fields'][fn])
                            else:
                                self.assertEqual(le['fields'][fi], ve['fields'][fn])
                total_transitions += len(v6_trans)
            self.assertEqual(total_transitions, 157)

            # Also verify fast_dispatch=True produces identical decisions/outputs across all 24 paths
            fast_chk_dir = root / 'lib_fast_chk'
            codegen_lib.generate_lib(
                model_path, fast_chk_dir, prefix='tcpip', byte_cap=2048, fast_dispatch=True, debug_names=True
            )
            diff_fast = root / 'diff_fast'
            _compile([
                CC, '-std=c99', '-Wall', '-Wextra', '-Werror', '-O2', '-I', str(fast_chk_dir),
                str(harness_c), str(fast_chk_dir / 'tcpip.c'), '-o', str(diff_fast),
            ])
            for case in reg['cases']:
                s_out = subprocess.check_output([str(diff_exe)], input=case['input'], text=True, timeout=30)
                f_out = subprocess.check_output([str(diff_fast)], input=case['input'], text=True, timeout=30)
                self.assertEqual(f_out, s_out, f"fast_dispatch mismatch on {case['id']}")

            # Throughput microbenchmark comparing c99-lib-v1 fast vs strict on 100,000 ECHO frames
            import time as _time
            bench_iters = 100000
            t0 = _time.perf_counter()
            subprocess.run([str(diff_fast), '--bench', str(bench_iters)], check=True, timeout=30)
            fast_ns = (_time.perf_counter() - t0) * 1e9 / bench_iters

            # Report .text sizes cleanly for M0 milestone baseline tracking
            sz_v6 = _text_size(v6_obj)
            sz_strict = _text_size(obj_s)
            sz_fast = _text_size(obj_f)
            print(
                f'\n[M0 metrics] v6.o .text={sz_v6}B | c99-lib-v1 strict .text={sz_strict}B | '
                f'c99-lib-v1 fast .text={sz_fast}B | fast_bench={fast_ns:.1f} ns/pkt '
                f'(switches={meta_s["decision_tree_switches"]})',
                flush=True,
            )


if __name__ == '__main__':
    unittest.main()
