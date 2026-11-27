"""High-performance, zero-copy C99 static-library backend (`c99-lib-v1`)."""
import argparse
from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path
import re
import sys

from protocol_lab.codegen import (
    KINDS,
    Unsupported,
    admit,
    cstr,
    dynamic_text,
    integer,
    string_literals,
)
from protocol_lab.ir import infer, load, model_files
from protocol_lab.model_identity import model_hash

HERE = Path(__file__).resolve().parent
BACKEND_NAME = 'c99-lib-v1'
DEFAULT_BYTE_CAP = 2048
DEFAULT_ARENA_CAP = 16384
MAX_BYTE_CAP = 65535
TEXT_CAP = 4096
TEXT_POOL_CAP = 64


def _sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def _sanitize_ident(text, upper=False):
    ident = re.sub(r'[^A-Za-z0-9]+', '_', text).strip('_')
    if not ident:
        ident = 'x'
    if ident[0].isdigit():
        ident = 'm_' + ident
    return ident.upper() if upper else ident.lower()


def _extract_eq_constraints(expr, model, strings):
    """Return {var_name: int64_const} from pure top-level `and` + `eq(var, literal)` guards."""
    out = {}

    def scalar_const(node):
        if type(node) is bool:
            return 1 if node else 0
        if type(node) is int:
            return node
        if type(node) is str:
            return strings.index(node)
        if type(node) is dict and set(node) == {'seq'}:
            return node['seq']
        return None

    def walk(node):
        if type(node) is not dict:
            return
        op = node.get('op')
        if op == 'and':
            for arg in node['args']:
                walk(arg)
            return
        if op == 'eq' and len(node['args']) == 2:
            a, b = node['args']
            for var_side, lit_side in ((a, b), (b, a)):
                if type(var_side) is dict and set(var_side) == {'var'}:
                    vname = var_side['var']
                    if model['variables'][vname]['type'] == 'bytes':
                        continue
                    cval = scalar_const(lit_side)
                    if cval is not None:
                        # Contradictory equality constraints keep the first safely ignored only if needed;
                        # store None sentinel if same variable must equal two distinct values.
                        if vname in out and out[vname] != cval:
                            out[vname] = None
                        else:
                            out[vname] = cval

    walk(expr)
    return {k: v for k, v in out.items() if v is not None}


def _partition_rules(rule_indices, constraints_by_rule, used_vars, min_leaf=4):
    """Build a sound discriminator tree over `rule_indices` preserving full fallback coverage."""
    if len(rule_indices) <= min_leaf:
        return ('leaf', list(rule_indices))

    best_var = None
    best_score = None
    candidate_vars = sorted({
        v for idx in rule_indices for v in constraints_by_rule[idx] if v not in used_vars
    })
    for v in candidate_vars:
        buckets = defaultdict(list)
        unconstrained = []
        for idx in rule_indices:
            if v in constraints_by_rule[idx]:
                buckets[constraints_by_rule[idx][v]].append(idx)
            else:
                unconstrained.append(idx)
        if len(buckets) < 2 and not unconstrained:
            continue
        if len(buckets) >= 2:
            # Prefer variables that leave fewest rules unconstrained and partition well.
            max_bucket = max(len(b) + len(unconstrained) for b in buckets.values())
            score = (len(unconstrained), max_bucket, -len(buckets), v)
            if best_score is None or score < best_score:
                best_score = score
                best_var = v

    if best_var is None:
        return ('leaf', list(rule_indices))

    buckets = defaultdict(list)
    unconstrained = []
    for idx in rule_indices:
        if best_var in constraints_by_rule[idx]:
            buckets[constraints_by_rule[idx][best_var]].append(idx)
        else:
            unconstrained.append(idx)

    # Preserve declaration order inside every case branch by filtering original `rule_indices`.
    next_used = used_vars | {best_var}
    unc_set = set(unconstrained)
    cases = []
    for val in sorted(buckets):
        allowed = set(buckets[val]) | unc_set
        branch_rules = [idx for idx in rule_indices if idx in allowed]
        cases.append((val, _partition_rules(branch_rules, constraints_by_rule, next_used, min_leaf)))
    default_node = _partition_rules(unconstrained, constraints_by_rule, next_used, min_leaf) if unconstrained else ('empty', [])
    return ('switch', best_var, cases, default_node)


def render(model, *, prefix='fsa_proto', byte_cap=DEFAULT_BYTE_CAP, arena_cap=DEFAULT_ARENA_CAP,
           fast_dispatch=False, debug_names=False):
    """Render `(header_text, source_text, metadata)` for an admitted Protocol IR model."""
    admit(model)
    if not re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*', prefix):
        raise Unsupported(f'Invalid C symbol prefix: {prefix}')
    if not (1 <= byte_cap <= MAX_BYTE_CAP):
        raise Unsupported(f'byte_cap must be 1..{MAX_BYTE_CAP}')
    if arena_cap < 512:
        raise Unsupported('arena_cap must be >= 512 bytes')

    pfx = prefix.lower()
    PFX = prefix.upper()
    states = model['states']
    variables = list(model['variables'])
    byte_vars = [n for n, v in model['variables'].items() if v['type'] == 'bytes']
    scalar_vars = [n for n, v in model['variables'].items() if v['type'] != 'bytes']
    events = list(model['events'])
    timers = list(model['timers'])
    messages = list(model['messages'])
    strings = string_literals(model)
    has_text = dynamic_text(model)
    if has_text:
        for s in strings:
            if len(s.encode('utf-8')) > TEXT_CAP:
                raise Unsupported(f'String literal exceeds TEXT_CAP={TEXT_CAP}')

    nsv = len(scalar_vars)
    nb = len(byte_vars)
    nt = len(timers)
    max_emits = max(
        (sum(1 for a in r['actions'] if next(iter(a)) in ('emit', 'emit_if')) for r in model['transitions']),
        default=0,
    )
    max_msg_fields = max((len(spec['fields']) for spec in model['messages'].values()), default=0)

    def unique_enum_names(names, kind_tag):
        used = {}
        out = []
        for idx, name in enumerate(names):
            base = f'{PFX}_{kind_tag}_{_sanitize_ident(name, upper=True)}'
            if base in used:
                base = f'{base}_{idx}'
            used[base] = True
            out.append((name, idx, base))
        return out

    state_enums = unique_enum_names(states, 'STATE')
    ev_enums = unique_enum_names(events, 'EV')
    msg_enums = unique_enum_names(messages, 'MSG')
    timer_enums = unique_enum_names(timers, 'TIMER')
    svar_enums = unique_enum_names(scalar_vars, 'SVAR')
    bvar_enums = unique_enum_names(byte_vars, 'BVAR')
    str_enums = unique_enum_names([s or 'EMPTY' for s in strings], 'STR')

    byte_lits = {}
    byte_lit_order = []

    def intern_byte_lit(vals):
        key = tuple(vals)
        if not key:
            return None
        if len(key) > byte_cap:
            raise Unsupported(f'Byte literal length {len(key)} exceeds byte_cap={byte_cap}')
        if key not in byte_lits:
            sym = f'{pfx}_lit_{len(byte_lit_order)}'
            byte_lits[key] = sym
            byte_lit_order.append((sym, key))
        return byte_lits[key]

    def exp_builder():
        counts = Counter()
        expr_keys = {}
        reps = {}
        shared = {}
        planning = True

        def expand(e, event=None):
            if type(e) is bool:
                return '1' if e else '0'
            if type(e) is int:
                return integer(e)
            if type(e) is str:
                return integer(strings.index(e))
            if 'seq' in e:
                return integer(e['seq'])
            if 'bytes' in e:
                sym = intern_byte_lit(e['bytes'])
                if sym is None:
                    return 'fsa_slice_make(NULL, 0U)'
                return f'fsa_slice_make({sym}, {len(e["bytes"])}U)'
            if 'var' in e:
                name = e['var']
                if name in byte_vars:
                    bi = byte_vars.index(name)
                    return f'fsa_slice_make(m->bdata[{bi}], m->blen[{bi}])'
                return f'm->v[{scalar_vars.index(name)}]'
            if 'event' in e:
                name = e['event']
                spec = model['events'][event]
                fi = list(spec['fields']).index(name)
                if spec['fields'][name] == 'bytes':
                    return f'ev[{fi}].bytes'
                return f'ev[{fi}].i64'
            if 'state' in e:
                return f'(m->state == {states.index(e["state"])})'
            if 'timer_active' in e:
                return f'(m->active[{timers.index(e["timer_active"])}] != 0)'

            args = [render_expr(x, event) for x in e['args']]
            op = e['op']
            if op in ('eq', 'ne') and infer(e['args'][0], model, event) == 'bytes':
                fn = f'fsa_slice_eq({args[0]}, {args[1]})'
                return fn if op == 'eq' else f'(!{fn})'
            if op == 'bytes_len':
                return f'((int64_t)({args[0]}).len)'
            if op == 'bytes_concat':
                return f'fsa_concat(arena, {args[0]}, {args[1]}, {PFX}_BYTE_CAP, err)'
            if op == 'bytes_slice':
                return f'fsa_slice_sub({args[0]}, {args[1]}, {args[2]}, {PFX}_BYTE_CAP, err)'
            if op == 'bytes_at_or_zero':
                return f'fsa_slice_at_or_zero({args[0]}, {args[1]}, {PFX}_BYTE_CAP, err)'
            if op == 'bytes_pack8_mod':
                return f'fsa_pack8(arena, {args[0]}, {PFX}_BYTE_CAP, err)'
            if op == 'bytes_pack16be_mod':
                return f'fsa_pack16be(arena, {args[0]}, {PFX}_BYTE_CAP, err)'
            if op == 'bytes_pack32be_mod':
                return f'fsa_pack32be(arena, {args[0]}, {PFX}_BYTE_CAP, err)'
            if op == 'bytes_internet_checksum16':
                return f'fsa_checksum16({args[0]}, {PFX}_BYTE_CAP, err)'
            binary = {'eq': '==', 'ne': '!=', 'le': '<=', 'ge': '>=', 'and': '&&', 'or': '||'}
            if op in binary:
                return f'({args[0]} {binary[op]} {args[1]})'
            if op == 'not':
                return f'(!{args[0]})'
            if op == 'implies':
                return f'(!{args[0]} || {args[1]})'
            if op == 'ite':
                return f'({args[0]} ? {args[1]} : {args[2]})'
            if op == 'seq_lt':
                return f'fsa_seq_lt({args[0]}, {args[1]})'
            if op == 'seq_le':
                return f'fsa_seq_le({args[0]}, {args[1]})'
            if op == 'seq_comparable':
                return f'fsa_seq_comparable({args[0]}, {args[1]})'
            if op == 'seq_add':
                return f'fsa_seq_add({args[0]}, {args[1]})'
            if op == 'seq_distance':
                return f'fsa_seq_dist({args[0]}, {args[1]})'
            if op == 'min':
                return f'fsa_min({args[0]}, {args[1]})'
            return {'add': 'fsa_add', 'sub': 'fsa_sub', 'mul': 'fsa_mul'}[op] + f'({args[0]}, {args[1]}, err)'

        def render_expr(e, event=None):
            compound = isinstance(e, dict) and 'op' in e
            if not planning and compound:
                key = expr_keys[(id(e), event)]
                if key in shared:
                    return f'{shared[key]}(m, ev, arena, err)'
            rendered = expand(e, event)
            if planning and compound:
                kind = 'fsa_slice_t' if infer(e, model, event) == 'bytes' else 'int64_t'
                key = (kind, rendered)
                expr_keys[(id(e), event)] = key
                counts[key] += 1
                reps.setdefault(key, (e, event))
            return rendered

        for r in model['transitions']:
            ev = r['event']
            render_expr(r['guard'], ev)
            for act in r['actions']:
                k, p = next(iter(act.items()))
                if k == 'set':
                    render_expr(p['value'], ev)
                elif k in ('emit', 'emit_if'):
                    for val_e in p['fields'].values():
                        render_expr(val_e, ev)
                elif k in ('arm', 'arm_if'):
                    render_expr(p['delay_ms'], ev)
                if k in ('emit_if', 'arm_if', 'cancel_if'):
                    render_expr(p['when'], ev)
        for inv in model['invariants']:
            render_expr(inv['assert'], None)

        min_expr_len = 52 if fast_dispatch else 80
        candidates = sorted((k for k, n in counts.items() if n >= 2 and len(k[1]) >= min_expr_len),
                            key=lambda k: (len(k[1]), k))
        shared = {k: f'{pfx}_expr_{i}' for i, k in enumerate(candidates)}
        planning = False
        return render_expr, expand, shared, reps

    exp, expand_body, shared_helpers, reps = exp_builder()

    # Build header
    h = [
        f'/* Generated by Formal-Spec-Agent ({BACKEND_NAME}) — do not edit manually. */',
        f'#ifndef {PFX}_H',
        f'#define {PFX}_H',
        '',
        '#include "fsa_lib_runtime.h"',
        '',
        f'#define {PFX}_BYTE_CAP {byte_cap}U',
        f'#define {PFX}_STEP_SCRATCH_BYTES {arena_cap}U',
        f'#define {PFX}_NUM_STATES {len(states)}',
        f'#define {PFX}_NUM_SCALAR_VARS {nsv}',
        f'#define {PFX}_NUM_BYTE_VARS {nb}',
        f'#define {PFX}_NUM_EVENTS {len(events)}',
        f'#define {PFX}_NUM_TIMERS {nt}',
        f'#define {PFX}_NUM_MESSAGES {len(messages)}',
        f'#define {PFX}_NUM_STRINGS {len(strings)}',
        f'#define {PFX}_NUM_RULES {len(model["transitions"])}',
        '',
        f'#ifndef {PFX}_CHECK_CONFLICTS',
        f'#ifdef FSA_STRICT',
        f'#define {PFX}_CHECK_CONFLICTS 1',
        f'#else',
        f'#define {PFX}_CHECK_CONFLICTS {0 if fast_dispatch else 1}',
        f'#endif',
        '#endif',
        f'#ifndef {PFX}_ATOMIC_ROLLBACK',
        f'#ifdef FSA_STRICT',
        f'#define {PFX}_ATOMIC_ROLLBACK 1',
        f'#else',
        f'#define {PFX}_ATOMIC_ROLLBACK {0 if fast_dispatch else 1}',
        f'#endif',
        '#endif',
        f'#ifndef {PFX}_CHECK_INVARIANTS',
        f'#ifdef FSA_STRICT',
        f'#define {PFX}_CHECK_INVARIANTS 1',
        f'#else',
        f'#define {PFX}_CHECK_INVARIANTS {0 if fast_dispatch else 1}',
        f'#endif',
        '#endif',
        f'#define {PFX}_HAS_TEXT_EVENTS {1 if has_text else 0}',
        '',
    ]

    if has_text:
        h.extend([
            f'#define {PFX}_TEXT_CAP {TEXT_CAP}',
            f'#define {PFX}_TEXT_POOL_CAP {TEXT_POOL_CAP}',
            'typedef struct {',
            '    int count;',
            f'    uint16_t len[{PFX}_TEXT_POOL_CAP];',
            f'    char data[{PFX}_TEXT_POOL_CAP][{PFX}_TEXT_CAP];',
            f'}} {pfx}_text_pool_t;',
            '',
        ])

    for title, pairs in (
        ('States', state_enums),
        ('Events', ev_enums),
        ('Messages', msg_enums),
        ('Timers', timer_enums),
        ('Scalar variables', svar_enums),
        ('Byte variables', bvar_enums),
        ('Static string literals', str_enums),
    ):
        if pairs:
            h.append(f'/* {title} */')
            h.append('enum {')
            for _, idx, sym in pairs:
                h.append(f'    {sym} = {idx},')
            h.append('};')
            h.append('')

    h.append(f'typedef struct {pfx}_machine {{')
    h.append('    int state;')
    h.append('    int64_t now_ms;')
    h.append(f'    int64_t v[{max(nsv, 1)}];')
    if nb > 0:
        h.append(f'    uint16_t blen[{nb}];')
        h.append(f'    uint8_t bdata[{nb}][{PFX}_BYTE_CAP];')
    if nt > 0:
        h.append(f'    int64_t due[{nt}];')
        h.append(f'    uint8_t active[{nt}];')
    if has_text:
        h.append(f'    {pfx}_text_pool_t texts;')
    h.append(f'}} {pfx}_machine_t;')
    h.append('')
    h.append(f'typedef void (*{pfx}_emit_fn)(void *ctx, int msg_id, const fsa_val_t *fields, int nfields);')
    h.append('')
    h.extend([
        f'int {pfx}_init({pfx}_machine_t *m);',
        f'int {pfx}_check_invariants(const {pfx}_machine_t *m);',
        f'int64_t {pfx}_next_due_ms(const {pfx}_machine_t *m);',
        f'int {pfx}_step_ws({pfx}_machine_t *m, int64_t now_ms, int event, '
        f'const fsa_val_t *args, int nargs, {pfx}_emit_fn on_emit, void *ctx, '
        f'fsa_arena_t *arena, {pfx}_machine_t *saved_buf, int *last_rule_out);',
        f'int {pfx}_step_with_arena({pfx}_machine_t *m, int64_t now_ms, int event, '
        f'const fsa_val_t *args, int nargs, {pfx}_emit_fn on_emit, void *ctx, '
        f'fsa_arena_t *arena, int *last_rule_out);',
        f'int {pfx}_step({pfx}_machine_t *m, int64_t now_ms, int event, '
        f'const fsa_val_t *args, int nargs, {pfx}_emit_fn on_emit, void *ctx, '
        f'int *last_rule_out);',
        f'int {pfx}_tick({pfx}_machine_t *m, int64_t now_ms, {pfx}_emit_fn on_emit, void *ctx);',
        f'int {pfx}_tick_one_ws({pfx}_machine_t *m, int64_t up_to_ms, {pfx}_emit_fn on_emit, void *ctx, '
        f'fsa_arena_t *arena, {pfx}_machine_t *saved_buf, int *last_rule_out);',
        f'int {pfx}_tick_one({pfx}_machine_t *m, int64_t up_to_ms, {pfx}_emit_fn on_emit, void *ctx, int *last_rule_out);',
        f'const char *{pfx}_string_literal(int64_t str_id);',
    ])
    if debug_names:
        h.extend([
            f'const char *{pfx}_state_name(int state_id);',
            f'const char *{pfx}_event_name(int event_id);',
            f'const char *{pfx}_rule_name(int rule_id);',
            f'const char *{pfx}_msg_name(int msg_id);',
            f'const char *{pfx}_svar_name(int var_id);',
            f'const char *{pfx}_bvar_name(int var_id);',
        ])
    h.extend(['', f'#endif /* {PFX}_H */', ''])

    # Build source
    c = [
        f'/* Generated by Formal-Spec-Agent ({BACKEND_NAME}) — do not edit manually. */',
        f'#include "{pfx}.h"',
        '',
    ]

    if strings:
        c.append(f'static const char *const {pfx}_str_table[{len(strings)}] = {{')
        for s in strings:
            c.append(f'    {cstr(s)},')
        c.append('};')
        c.append(f'static const uint16_t {pfx}_str_len[{len(strings)}] = {{')
        c.append('    ' + ', '.join(f'{len(s.encode("utf-8"))}U' for s in strings))
        c.append('};')
    else:
        c.append(f'static const char *const {pfx}_str_table[1] = {{ "" }};')
        c.append(f'static const uint16_t {pfx}_str_len[1] = {{ 0U }};')
    c.append('')
    c.append(f'const char *{pfx}_string_literal(int64_t str_id) {{')
    c.append(f'    (void){pfx}_str_len;')
    if strings:
        c.append(f'    if (str_id < 0 || str_id >= {PFX}_NUM_STRINGS) return "";')
        c.append(f'    return {pfx}_str_table[str_id];')
    else:
        c.append(f'    (void)str_id; (void){pfx}_str_table;')
        c.append('    return "";')
    c.append('}')
    c.append('')

    for sym, vals in byte_lit_order:
        raw = ', '.join(str(b) for b in vals)
        c.append(f'static const uint8_t {sym}[{len(vals)}] = {{ {raw} }};')
    if byte_lit_order:
        c.append('')

    if has_text:
        c.extend([
            f'static int {pfx}_text_find(const {pfx}_text_pool_t *pool, const uint8_t *s, size_t n) {{',
            '    for (int i = 0; i < pool->count; i++) {',
            '        if ((size_t)pool->len[i] == n && (n == 0 || memcmp(pool->data[i], s, n) == 0)) return i;',
            '    }',
            '    return -1;',
            '}',
            f'static int {pfx}_text_add({pfx}_text_pool_t *pool, const uint8_t *s, size_t n, int *err) {{',
            f'    if (!fsa_valid_utf8(s, n)) {{ if (!*err) *err = FSA_ERR_INVALID_ARG; return -1; }}',
            f'    int idx = {pfx}_text_find(pool, s, n);',
            '    if (idx >= 0) return idx;',
            f'    if (n > (size_t){PFX}_TEXT_CAP || pool->count >= {PFX}_TEXT_POOL_CAP) {{ if (!*err) *err = FSA_ERR_TEXT_CAP; return -1; }}',
            '    if (n) memcpy(pool->data[pool->count], s, n);',
            '    pool->len[pool->count] = (uint16_t)n;',
            '    return pool->count++;',
            '}',
            '',
        ])

    if debug_names:
        def emit_name_fn(fn_name, names):
            c.append(f'const char *{pfx}_{fn_name}(int id) {{')
            if names:
                c.append(f'    static const char *const tbl[{len(names)}] = {{ {", ".join(cstr(n) for n in names)} }};')
                c.append(f'    return (id >= 0 && id < {len(names)}) ? tbl[id] : "";')
            else:
                c.append('    (void)id; return "";')
            c.append('}')
        emit_name_fn('state_name', states)
        emit_name_fn('event_name', events)
        emit_name_fn('rule_name', [r['id'] for r in model['transitions']])
        emit_name_fn('msg_name', messages)
        emit_name_fn('svar_name', scalar_vars)
        emit_name_fn('bvar_name', byte_vars)
        c.append('')

    # Metadata tables
    ev_n = max(len(events), 1)
    c.append(f'static const uint8_t {pfx}_event_origin[{ev_n}] = {{ ' +
             (', '.join('1U' if model['events'][e]['origin'] == 'timer' else '0U' for e in events) if events else '0U') + ' };')
    c.append(f'static const int {pfx}_event_nfields[{ev_n}] = {{ ' +
             (', '.join(str(len(model['events'][e]['fields'])) for e in events) if events else '0') + ' };')
    max_ef = max((len(model['events'][e]['fields']) for e in events), default=1)
    c.append(f'static const uint8_t {pfx}_event_kinds[{ev_n}][{max(max_ef, 1)}] = {{')
    if events:
        for e in events:
            row = [str(KINDS[k]) for k in model['events'][e]['fields'].values()] or ['0']
            c.append('    { ' + ', '.join(row) + ' },')
    else:
        c.append('    { 0 },')
    c.append('};')
    if nt > 0:
        c.append(f'static const int {pfx}_timer_events[{nt}] = {{ ' +
                 ', '.join(str(events.index(model['timers'][t]['event'])) for t in timers) + ' };')
        if nt > 1:
            c.append(f'static const char *const {pfx}_timer_names[{nt}] = {{ ' +
                     ', '.join(cstr(t) for t in timers) + ' };')
    c.append('')

    # Non-inline shared pure helpers reduce code bloat dramatically under -Os
    for (kind, _), fname in shared_helpers.items():
        e, ev = reps[(kind, _)]
        body = expand_body(e, ev)
        c.append(
            f'static {kind} {fname}(const {pfx}_machine_t *m, const fsa_val_t *ev, '
            f'fsa_arena_t *arena, int *err) {{'
        )
        c.append('    (void)m; (void)ev; (void)arena; (void)err;')
        c.append(f'    return {body};')
        c.append('}')
    if shared_helpers:
        c.append('')

    # Invariants
    c.append(f'static int {pfx}_check_inv_err(const {pfx}_machine_t *m, fsa_arena_t *arena, int *err) {{')
    c.append('    const fsa_val_t *ev = NULL;')
    c.append('    (void)m; (void)ev; (void)arena; (void)err;')
    for inv in model['invariants']:
        cond = exp(inv['assert'], None)
        c.append(f'    if (!({cond})) {{ if (!*err) *err = FSA_ERR_INVARIANT; return 0; }}')
        c.append('    if (*err) return 0;')
    c.append('    return *err == FSA_OK;')
    c.append('}')
    c.append('')
    c.append(f'int {pfx}_check_invariants(const {pfx}_machine_t *m) {{')
    c.append('    int err = FSA_OK;')
    c.append(f'    uint8_t scratch[{PFX}_STEP_SCRATCH_BYTES];')
    c.append(f'    fsa_arena_t arena = {{ scratch, 0U, {PFX}_STEP_SCRATCH_BYTES }};')
    c.append('    if (!m) return -FSA_ERR_INVALID_ARG;')
    c.append(f'    if (!{pfx}_check_inv_err(m, &arena, &err)) return err ? -err : -FSA_ERR_INVARIANT;')
    c.append('    return FSA_OK;')
    c.append('}')
    c.append('')

    # Init
    c.append(f'int {pfx}_init({pfx}_machine_t *m) {{')
    c.append('    int err = FSA_OK;')
    c.append('    if (!m) return -FSA_ERR_INVALID_ARG;')
    c.append('    memset(m, 0, sizeof(*m));')
    c.append(f'    m->state = {states.index(model["initial_state"])};')
    if has_text:
        for s in strings:
            b = s.encode('utf-8')
            raw = ','.join(str(x) for x in b) or '0'
            c.append(f'    {pfx}_text_add(&m->texts, (const uint8_t[]){{{raw}}}, {len(b)}U, &err);')
    for n in scalar_vars:
        idx = scalar_vars.index(n)
        init_val = model['variables'][n]['initial']
        c.append(f'    m->v[{idx}] = {exp(init_val)};')
    for n in byte_vars:
        bi = byte_vars.index(n)
        init_bytes = model['variables'][n]['initial']
        if len(init_bytes) > byte_cap:
            raise Unsupported(f'Initial byte variable {n} exceeds byte_cap={byte_cap}')
        if init_bytes:
            raw = ','.join(str(x) for x in init_bytes)
            c.append(
                f'    fsa_buf_assign(m->bdata[{bi}], &m->blen[{bi}], {PFX}_BYTE_CAP, '
                f'fsa_slice_make((const uint8_t[]){{{raw}}}, {len(init_bytes)}U), &err);'
            )
    c.append('    if (err) return -err;')
    c.append(f'    return {pfx}_check_invariants(m);')
    c.append('}')
    c.append('')

    # Emit helper for rule fields
    if max_emits > 0:
        c.append('typedef struct {')
        c.append('    int msg_id;')
        c.append('    int nfields;')
        c.append(f'    fsa_val_t fields[{max(max_msg_fields, 1)}];')
        c.append(f'}} {pfx}_pending_emit_t;')
        c.append('')

    # Guard functions & Action functions
    for i, r in enumerate(model['transitions']):
        ev = r['event']
        c.append(
            f'static int {pfx}_guard_{i}(const {pfx}_machine_t *m, const fsa_val_t *ev, '
            f'fsa_arena_t *arena, int *err) {{'
        )
        c.append('    (void)m; (void)ev; (void)arena; (void)err;')
        c.append(f'    return ({exp(r["guard"], ev)}) != 0;')
        c.append('}')
    c.append('')

    for i, r in enumerate(model['transitions']):
        ev = r['event']
        rule_emits = sum(1 for a in r['actions'] if next(iter(a)) in ('emit', 'emit_if'))
        c.append(
            f'static int {pfx}_action_{i}({pfx}_machine_t *m, const fsa_val_t *ev, '
            f'fsa_arena_t *arena, {pfx}_emit_fn on_emit, void *ctx, int *err) {{'
        )
        c.append('    (void)m; (void)ev; (void)arena; (void)on_emit; (void)ctx; (void)err;')
        if rule_emits > 0:
            c.append(f'    {pfx}_pending_emit_t emits[{rule_emits}];')
            c.append('    int nemits = 0;')
            c.append('    memset(emits, 0, sizeof(emits));')
        for act in r['actions']:
            k, p = next(iter(act.items()))
            if k == 'set':
                name = p['var']
                val_c = exp(p['value'], ev)
                if name in byte_vars:
                    bi = byte_vars.index(name)
                    c.append(f'    fsa_buf_assign(m->bdata[{bi}], &m->blen[{bi}], {PFX}_BYTE_CAP, {val_c}, err);')
                else:
                    si = scalar_vars.index(name)
                    c.append(f'    m->v[{si}] = {val_c};')
            elif k in ('emit', 'emit_if'):
                indent = '    '
                if k == 'emit_if':
                    c.append(f'    if ({exp(p["when"], ev)}) {{')
                    indent = '        '
                msg_name = p['message']
                mid = messages.index(msg_name)
                mfields = model['messages'][msg_name]['fields']
                c.append(f'{indent}if (!*err) {{')
                c.append(f'{indent}    {pfx}_pending_emit_t *pe = &emits[nemits++];')
                c.append(f'{indent}    pe->msg_id = {mid};')
                c.append(f'{indent}    pe->nfields = {len(mfields)};')
                for j, (fname, fkind) in enumerate(mfields.items()):
                    val_c = exp(p['fields'][fname], ev)
                    if fkind == 'bytes':
                        c.append(f'{indent}    {{ fsa_slice_t _bs = {val_c};')
                        c.append(f'{indent}      if ((size_t)_bs.len > (size_t){PFX}_BYTE_CAP) {{ if (!*err) *err = FSA_ERR_BYTE_CAP; }}')
                        c.append(
                            f'{indent}      else if (on_emit) {{ pe->fields[{j}] = fsa_val_bytes(NULL, 0); '
                            f'pe->fields[{j}].bytes = fsa_arena_copy(arena, _bs, {PFX}_BYTE_CAP, err); }}'
                        )
                        c.append(f'{indent}    }}')
                    elif fkind == 'bool':
                        c.append(f'{indent}    pe->fields[{j}] = fsa_val_bool((int)({val_c}));')
                    elif fkind == 'seq32':
                        c.append(f'{indent}    pe->fields[{j}] = fsa_val_seq32((uint32_t)({val_c}));')
                    elif fkind == 'string':
                        c.append(f'{indent}    {{ int64_t sid = {val_c};')
                        if has_text:
                            c.append(
                                f'{indent}      if (sid < 0 || sid >= m->texts.count) {{ if (!*err) *err = FSA_ERR_STRING_DOMAIN; }}'
                            )
                            c.append(
                                f'{indent}      else if (on_emit) {{ pe->fields[{j}] = fsa_val_str(m->texts.data[sid], m->texts.len[sid]); pe->fields[{j}].i64 = sid; }}'
                            )
                        else:
                            c.append(
                                f'{indent}      if (sid < 0 || sid >= {PFX}_NUM_STRINGS) {{ if (!*err) *err = FSA_ERR_STRING_DOMAIN; }}'
                            )
                            c.append(
                                f'{indent}      else if (on_emit) {{ pe->fields[{j}] = fsa_val_str({pfx}_str_table[sid], {pfx}_str_len[sid]); pe->fields[{j}].i64 = sid; }}'
                            )
                        c.append(f'{indent}    }}')
                    else:
                        c.append(f'{indent}    pe->fields[{j}] = fsa_val_int({val_c});')
                c.append(f'{indent}}}')
                if k == 'emit_if':
                    c.append('    }')
            elif k in ('arm', 'arm_if'):
                ti = timers.index(p['timer'])
                indent = '    '
                if k == 'arm_if':
                    c.append(f'    if ({exp(p["when"], ev)}) {{')
                    indent = '        '
                else:
                    c.append('    {')
                    indent = '        '
                c.append(f'{indent}int64_t delay = {exp(p["delay_ms"], ev)};')
                c.append(f'{indent}if (delay <= 0) {{ if (!*err) *err = FSA_ERR_TIMER_DELAY; return 0; }}')
                c.append(f'{indent}m->due[{ti}] = fsa_add(m->now_ms, delay, err);')
                c.append(f'{indent}m->active[{ti}] = 1U;')
                c.append('    }')
            elif k in ('cancel', 'cancel_if'):
                tname = p if k == 'cancel' else p['timer']
                ti = timers.index(tname)
                if k == 'cancel_if':
                    c.append(f'    if ({exp(p["when"], ev)}) m->active[{ti}] = 0U;')
                else:
                    c.append(f'    m->active[{ti}] = 0U;')
            c.append('    if (*err) return 0;')
        c.append(f'    m->state = {states.index(r["to"])};')
        c.append(f'#if {PFX}_CHECK_INVARIANTS')
        c.append(f'    if (!{pfx}_check_inv_err(m, arena, err)) return 0;')
        c.append('#endif')
        if rule_emits > 0:
            c.append('    if (on_emit) {')
            c.append('        for (int k = 0; k < nemits; k++) {')
            c.append('            on_emit(ctx, emits[k].msg_id, emits[k].fields, emits[k].nfields);')
            c.append('        }')
            c.append('    }')
        c.append('    return *err == FSA_OK;')
        c.append('}')
        c.append('')

    # Precompute decision trees per (state_idx, event_idx)
    constraints_by_rule = [_extract_eq_constraints(r['guard'], model, strings) for r in model['transitions']]
    buckets_se = defaultdict(list)
    for idx, r in enumerate(model['transitions']):
        buckets_se[(states.index(r['from']), events.index(r['event']))].append(idx)

    def emit_leaf_eval(lines_out, rules_list, ind):
        if not rules_list:
            return
        lines_out.append(f'{ind}#if {PFX}_CHECK_CONFLICTS')
        for ridx in rules_list:
            lines_out.append(
                f'{ind}arena->used = saved_used; if ({pfx}_guard_{ridx}(m, ev, arena, err)) {{ match = {ridx}; count++; }}'
            )
        lines_out.append(f'{ind}#else')
        for ridx in rules_list:
            lines_out.append(
                f'{ind}arena->used = saved_used; if ({pfx}_guard_{ridx}(m, ev, arena, err)) {{ match = {ridx}; goto matched; }}'
            )
        lines_out.append(f'{ind}#endif')

    def emit_tree(lines_out, node, ind):
        tag = node[0]
        if tag == 'empty':
            return
        if tag == 'leaf':
            emit_leaf_eval(lines_out, node[1], ind)
            return
        _, var_name, cases, default_node = node
        sv_idx = scalar_vars.index(var_name)
        lines_out.append(f'{ind}switch (m->v[{sv_idx}]) {{')
        for val, child in cases:
            lines_out.append(f'{ind}    case {integer(val)}: {{')
            emit_tree(lines_out, child, ind + '        ')
            lines_out.append(f'{ind}        break;')
            lines_out.append(f'{ind}    }}')
        if default_node[0] != 'empty':
            lines_out.append(f'{ind}    default: {{')
            emit_tree(lines_out, default_node, ind + '        ')
            lines_out.append(f'{ind}        break;')
            lines_out.append(f'{ind}    }}')
        lines_out.append(f'{ind}}}')

    if events or nt > 0:
        # Fast O(1) decision-tree fire dispatcher
        c.append(
            f'static int {pfx}_fire({pfx}_machine_t *m, int event, const fsa_val_t *ev, '
            f'int expiring, fsa_arena_t *arena, {pfx}_emit_fn on_emit, void *ctx, int *last_rule_out, int *err) {{'
        )
        c.append('    (void)event; (void)ev; (void)on_emit; (void)ctx; (void)last_rule_out;')
        c.append('    int match = -1;')
        c.append(f'#if {PFX}_CHECK_CONFLICTS')
        c.append('    int count = 0;')
        c.append('#endif')
        c.append('    uint32_t saved_used = arena->used;')
        c.append('    switch (m->state) {')
        for sidx, sname in enumerate(states):
            c.append(f'        case {sidx}: {{')
            ev_keys = sorted(ev_i for (st_i, ev_i) in buckets_se if st_i == sidx)
            if ev_keys:
                c.append('            switch (event) {')
                for ev_i in ev_keys:
                    rules_list = buckets_se[(sidx, ev_i)]
                    tree = _partition_rules(rules_list, constraints_by_rule, set())
                    c.append(f'                case {ev_i}: {{')
                    emit_tree(c, tree, '                    ')
                    c.append('                    break;')
                    c.append('                }')
                c.append('                default: break;')
                c.append('            }')
            c.append('            break;')
            c.append('        }')
        c.append('        default: break;')
        c.append('    }')
        if model['transitions']:
            c.append(f'#if !{PFX}_CHECK_CONFLICTS')
            c.append('    goto done_scan;')
            c.append('matched:')
            c.append('    (void)0;')
            c.append('done_scan:')
            c.append('#endif')
        c.append('    if (*err) return 0;')
        c.append(f'#if {PFX}_CHECK_CONFLICTS')
        c.append('    if (count != 1) { *err = count ? FSA_ERR_CONFLICT : FSA_ERR_UNCOVERED; return 0; }')
        c.append('#else')
        c.append('    if (match < 0) { *err = FSA_ERR_UNCOVERED; return 0; }')
        c.append('#endif')
        if nt > 0:
            c.append('    if (expiring >= 0) m->active[expiring] = 0U;')
        else:
            c.append('    (void)expiring;')
        c.append('    if (last_rule_out) *last_rule_out = match;')
        c.append('    arena->used = saved_used;')
        c.append('    switch (match) {')
        for i in range(len(model['transitions'])):
            c.append(f'        case {i}: return {pfx}_action_{i}(m, ev, arena, on_emit, ctx, err);')
        c.append('        default: *err = FSA_ERR_INVALID_ARG; return 0;')
        c.append('    }')
        c.append('}')
        c.append('')

    # Timer query & advance
    c.append(f'int64_t {pfx}_next_due_ms(const {pfx}_machine_t *m) {{')
    if nt == 0:
        c.append('    (void)m; return -1;')
    elif nt == 1:
        c.append('    if (!m) return -1;')
        c.append('    return m->active[0] ? m->due[0] : -1;')
    else:
        c.append('    int next = -1;')
        c.append('    if (!m) return -1;')
        c.append(f'    for (int i = 0; i < {nt}; i++) {{')
        c.append('        if (m->active[i] && (next < 0 || m->due[i] < m->due[next])) next = i;')
        c.append('    }')
        c.append('    return next >= 0 ? m->due[next] : -1;')
    c.append('}')
    c.append('')

    c.append(
        f'static int {pfx}_advance_one({pfx}_machine_t *m, int64_t at_ms, fsa_arena_t *arena, '
        f'{pfx}_emit_fn on_emit, void *ctx, int *last_rule_out, int *err) {{'
    )
    c.append('    if (at_ms < m->now_ms) { *err = FSA_ERR_NONMONOTONIC; return -1; }')
    if nt == 0:
        c.append('    (void)arena; (void)on_emit; (void)ctx; (void)last_rule_out; (void)err;')
        c.append('    m->now_ms = at_ms;')
        c.append('    return 0;')
    elif nt == 1:
        c.append('    if (!m->active[0] || m->due[0] > at_ms) {')
        c.append('        m->now_ms = at_ms;')
        c.append('        return 0;')
        c.append('    }')
        c.append('    m->now_ms = m->due[0];')
        c.append('    arena->used = 0U;')
        c.append(f'    if (!{pfx}_fire(m, {pfx}_timer_events[0], NULL, 0, arena, on_emit, ctx, last_rule_out, err)) return -1;')
        c.append('    return 1;')
    else:
        c.append('    int next = -1;')
        c.append(f'    for (int i = 0; i < {nt}; i++) {{')
        c.append('        if (m->active[i] && (next < 0 || m->due[i] < m->due[next] ||')
        c.append(f'            (m->due[i] == m->due[next] && strcmp({pfx}_timer_names[i], {pfx}_timer_names[next]) < 0))) next = i;')
        c.append('    }')
        c.append('    if (next < 0 || m->due[next] > at_ms) {')
        c.append('        m->now_ms = at_ms;')
        c.append('        return 0;')
        c.append('    }')
        c.append('    m->now_ms = m->due[next];')
        c.append('    arena->used = 0U;')
        c.append(f'    if (!{pfx}_fire(m, {pfx}_timer_events[next], NULL, next, arena, on_emit, ctx, last_rule_out, err)) return -1;')
        c.append('    return 1;')
    c.append('}')
    c.append('')

    c.append(
        f'static int {pfx}_advance({pfx}_machine_t *m, int64_t at_ms, fsa_arena_t *arena, '
        f'{pfx}_emit_fn on_emit, void *ctx, int *err) {{'
    )
    if nt == 0:
        c.append(f'    return {pfx}_advance_one(m, at_ms, arena, on_emit, ctx, NULL, err) >= 0;')
    else:
        c.append('    int steps = 0;')
        c.append('    for (;;) {')
        c.append(f'        if (steps >= 4096) {{ int64_t nd = {pfx}_next_due_ms(m); if (nd >= 0 && nd <= at_ms) {{ *err = FSA_ERR_TIMER_STEPS; return 0; }} }}')
        c.append(f'        int rc = {pfx}_advance_one(m, at_ms, arena, on_emit, ctx, NULL, err);')
        c.append('        if (rc < 0) return 0;')
        c.append('        if (rc == 0) break;')
        c.append('        steps++;')
        c.append('    }')
        c.append('    return 1;')
    c.append('}')
    c.append('')

    # Step & tick entrypoints
    c.append(
        f'int {pfx}_step_ws({pfx}_machine_t *m, int64_t now_ms, int event, '
        f'const fsa_val_t *args, int nargs, {pfx}_emit_fn on_emit, void *ctx, '
        f'fsa_arena_t *arena, {pfx}_machine_t *saved_buf, int *last_rule_out) {{'
    )
    c.append('    int err = FSA_OK;')
    if events:
        c.append(f'    fsa_val_t ev_norm[{max(max_ef, 1)}];')
        c.append('    memset(ev_norm, 0, sizeof(ev_norm));')
    c.append('    if (!m || !arena || !arena->buf) return -FSA_ERR_INVALID_ARG;')
    c.append('    if (last_rule_out) *last_rule_out = -1;')
    if not events:
        c.append(f'    (void){pfx}_event_origin; (void){pfx}_event_nfields; (void){pfx}_event_kinds; (void)args;')
        c.append('    if (event >= 0 || nargs != 0) return -FSA_ERR_INVALID_ARG;')
    else:
        c.append('    if (event >= 0) {')
        c.append(f'        if (event >= {PFX}_NUM_EVENTS) return -FSA_ERR_INVALID_ARG;')
        c.append(f'        if ({pfx}_event_origin[event]) return -FSA_ERR_INVALID_ARG;')
        c.append(f'        if (nargs != {pfx}_event_nfields[event] || (nargs > 0 && !args)) return -FSA_ERR_INVALID_ARG;')
        c.append('    } else if (nargs != 0) {')
        c.append('        return -FSA_ERR_INVALID_ARG;')
        c.append('    }')
    c.append(f'#if {PFX}_ATOMIC_ROLLBACK')
    c.append('    if (!saved_buf) return -FSA_ERR_INVALID_ARG;')
    c.append('    *saved_buf = *m;')
    c.append('#else')
    c.append('    (void)saved_buf;')
    c.append('#endif')
    if events:
        c.append('    if (event >= 0) {')
        c.append('        for (int i = 0; i < nargs; i++) {')
        c.append(f'            uint8_t k = {pfx}_event_kinds[event][i];')
        c.append('            if (args[i].kind != k) { err = FSA_ERR_INVALID_ARG; goto fail; }')
        c.append('            ev_norm[i] = args[i];')
        c.append(f'            if (k == FSA_KIND_BYTES) {{ if (args[i].bytes.len > 0 && !args[i].bytes.ptr) {{ err = FSA_ERR_INVALID_ARG; goto fail; }} if ((size_t)args[i].bytes.len > (size_t){PFX}_BYTE_CAP) {{ err = FSA_ERR_BYTE_CAP; goto fail; }} }}')
        c.append('            else if (k == FSA_KIND_BOOL) { if (args[i].i64 != 0 && args[i].i64 != 1) { err = FSA_ERR_INVALID_ARG; goto fail; } }')
        c.append('            else if (k == FSA_KIND_SEQ32) { if (args[i].i64 < 0 || args[i].i64 >= FSA_SEQ_MOD) { err = FSA_ERR_INVALID_ARG; goto fail; } }')
        if has_text:
            c.append('            else if (k == FSA_KIND_STRING) {')
            c.append('                if (args[i].bytes.ptr) {')
            c.append(f'                    int sid = {pfx}_text_add(&m->texts, args[i].bytes.ptr, args[i].bytes.len, &err);')
            c.append('                    if (err) goto fail;')
            c.append('                    ev_norm[i].i64 = (int64_t)sid;')
            c.append('                } else if (args[i].bytes.len > 0) {')
            c.append('                    err = FSA_ERR_INVALID_ARG; goto fail;')
            c.append('                } else if (args[i].i64 < 0 || args[i].i64 >= m->texts.count) {')
            c.append('                    err = FSA_ERR_STRING_DOMAIN; goto fail;')
            c.append('                }')
            c.append('            }')
        else:
            c.append('            else if (k == FSA_KIND_STRING) { err = FSA_ERR_STRING_DOMAIN; goto fail; }')
        c.append('        }')
        c.append('    }')
    c.append(f'    if (!{pfx}_advance(m, now_ms, arena, on_emit, ctx, &err)) goto fail;')
    c.append('    arena->used = 0U;')
    if events:
        c.append('    if (event >= 0) {')
        c.append(f'        if (!{pfx}_fire(m, event, ev_norm, -1, arena, on_emit, ctx, last_rule_out, &err)) goto fail;')
        c.append('    }')
        c.append(f'#if {PFX}_CHECK_INVARIANTS')
        c.append('    else {')
        c.append(f'        if (!{pfx}_check_inv_err(m, arena, &err)) goto fail;')
        c.append('    }')
        c.append('#endif')
    else:
        c.append(f'#if {PFX}_CHECK_INVARIANTS')
        c.append(f'    if (!{pfx}_check_inv_err(m, arena, &err)) goto fail;')
        c.append('#endif')
    c.append('    return FSA_OK;')
    c.append('fail:')
    c.append(f'#if {PFX}_ATOMIC_ROLLBACK')
    c.append('    *m = *saved_buf;')
    c.append('#endif')
    c.append('    return err ? -err : -FSA_ERR_INVALID_ARG;')
    c.append('}')
    c.append('')

    c.extend([
        f'int {pfx}_step_with_arena({pfx}_machine_t *m, int64_t now_ms, int event, '
        f'const fsa_val_t *args, int nargs, {pfx}_emit_fn on_emit, void *ctx, '
        f'fsa_arena_t *arena, int *last_rule_out) {{',
        f'#if {PFX}_ATOMIC_ROLLBACK',
        f'    {pfx}_machine_t saved_local;',
        f'    return {pfx}_step_ws(m, now_ms, event, args, nargs, on_emit, ctx, arena, &saved_local, last_rule_out);',
        '#else',
        f'    return {pfx}_step_ws(m, now_ms, event, args, nargs, on_emit, ctx, arena, NULL, last_rule_out);',
        '#endif',
        '}',
        '',
        f'int {pfx}_step({pfx}_machine_t *m, int64_t now_ms, int event, '
        f'const fsa_val_t *args, int nargs, {pfx}_emit_fn on_emit, void *ctx, int *last_rule_out) {{',
        f'    uint8_t scratch[{PFX}_STEP_SCRATCH_BYTES];',
        f'    fsa_arena_t arena = {{ scratch, 0U, {PFX}_STEP_SCRATCH_BYTES }};',
        f'    return {pfx}_step_with_arena(m, now_ms, event, args, nargs, on_emit, ctx, &arena, last_rule_out);',
        '}',
        '',
        f'int {pfx}_tick({pfx}_machine_t *m, int64_t now_ms, {pfx}_emit_fn on_emit, void *ctx) {{',
        f'    return {pfx}_step(m, now_ms, -1, NULL, 0, on_emit, ctx, NULL);',
        '}',
        '',
        f'int {pfx}_tick_one_ws({pfx}_machine_t *m, int64_t up_to_ms, {pfx}_emit_fn on_emit, void *ctx, '
        f'fsa_arena_t *arena, {pfx}_machine_t *saved_buf, int *last_rule_out) {{',
        '    int err = FSA_OK;',
        '    if (!m || !arena || !arena->buf) return -FSA_ERR_INVALID_ARG;',
        '    if (last_rule_out) *last_rule_out = -1;',
        f'#if {PFX}_ATOMIC_ROLLBACK',
        '    if (!saved_buf) return -FSA_ERR_INVALID_ARG;',
        '    *saved_buf = *m;',
        '#else',
        '    (void)saved_buf;',
        '#endif',
        f'    int rc = {pfx}_advance_one(m, up_to_ms, arena, on_emit, ctx, last_rule_out, &err);',
        '    if (rc < 0) {',
        f'#if {PFX}_ATOMIC_ROLLBACK',
        '        *m = *saved_buf;',
        '#endif',
        '        return err ? -err : -FSA_ERR_INVALID_ARG;',
        '    }',
        '    return rc;',
        '}',
        '',
        f'int {pfx}_tick_one({pfx}_machine_t *m, int64_t up_to_ms, {pfx}_emit_fn on_emit, void *ctx, int *last_rule_out) {{',
        f'    uint8_t scratch[{PFX}_STEP_SCRATCH_BYTES];',
        f'    fsa_arena_t arena = {{ scratch, 0U, {PFX}_STEP_SCRATCH_BYTES }};',
        f'#if {PFX}_ATOMIC_ROLLBACK',
        f'    {pfx}_machine_t saved_local;',
        f'    return {pfx}_tick_one_ws(m, up_to_ms, on_emit, ctx, &arena, &saved_local, last_rule_out);',
        '#else',
        f'    return {pfx}_tick_one_ws(m, up_to_ms, on_emit, ctx, &arena, NULL, last_rule_out);',
        '#endif',
        '}',
        '',
    ])

    meta = {
        'backend': BACKEND_NAME,
        'protocol': model['protocol'],
        'prefix': pfx,
        'byte_cap': byte_cap,
        'arena_cap': arena_cap,
        'fast_dispatch': bool(fast_dispatch),
        'debug_names': bool(debug_names),
        'has_text_events': bool(has_text),
        'states': len(states),
        'scalar_vars': nsv,
        'byte_vars': nb,
        'timers': nt,
        'rules': len(model['transitions']),
        'shared_helpers': len(shared_helpers),
        'decision_tree_switches': sum(
            1 for k, r in buckets_se.items()
            if _partition_rules(r, constraints_by_rule, set())[0] == 'switch'
        ),
    }
    return '\n'.join(h), '\n'.join(c), meta


def generate_lib(model_file, out, *, prefix='fsa_proto', byte_cap=DEFAULT_BYTE_CAP,
                 arena_cap=DEFAULT_ARENA_CAP, fast_dispatch=False, debug_names=False):
    """Generate `<prefix>.h`, `<prefix>.c`, `fsa_lib_runtime.h`, and `generation.json`."""
    model_file = Path(model_file).resolve()
    out = Path(out).resolve()
    if out.exists():
        raise ValueError('Fresh output directory required')
    paths = model_files(model_file) + [HERE / 'codegen_lib.py', HERE / 'codegen_lib_runtime.h']
    inputs = {str(p): _sha256(p) for p in paths}
    m = load(model_file)
    h_text, c_text, meta = render(
        m, prefix=prefix, byte_cap=byte_cap, arena_cap=arena_cap,
        fast_dispatch=fast_dispatch, debug_names=debug_names,
    )
    if any(_sha256(p) != digest for p, digest in inputs.items()):
        raise ValueError('Input changed during codegen-lib')
    out.mkdir(parents=True)
    rt_bytes = (HERE / 'codegen_lib_runtime.h').read_bytes()
    (out / 'fsa_lib_runtime.h').write_bytes(rt_bytes)
    (out / f'{meta["prefix"]}.h').write_text(h_text, encoding='utf-8')
    (out / f'{meta["prefix"]}.c').write_text(c_text, encoding='utf-8')
    result = {
        'schema': 'fsa-codegen-lib-v1',
        'model_file': str(model_file),
        'model_semantic_sha256': model_hash(m),
        'inputs': inputs,
        'outputs': {
            'fsa_lib_runtime.h': _sha256(out / 'fsa_lib_runtime.h'),
            f'{meta["prefix"]}.h': _sha256(out / f'{meta["prefix"]}.h'),
            f'{meta["prefix"]}.c': _sha256(out / f'{meta["prefix"]}.c'),
        },
        **meta,
    }
    (out / 'generation.json').write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    return result


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('model', type=Path)
    p.add_argument('--out', type=Path, required=True)
    p.add_argument('--prefix', default='fsa_proto')
    p.add_argument('--byte-cap', type=int, default=DEFAULT_BYTE_CAP)
    p.add_argument('--arena-cap', type=int, default=DEFAULT_ARENA_CAP)
    grp = p.add_mutually_exclusive_group()
    grp.add_argument('--fast-dispatch', action='store_true')
    grp.add_argument('--strict-dispatch', action='store_true')
    p.add_argument('--debug-names', action='store_true')
    a = p.parse_args(argv)
    try:
        res = generate_lib(
            a.model, a.out, prefix=a.prefix, byte_cap=a.byte_cap,
            arena_cap=a.arena_cap, fast_dispatch=a.fast_dispatch, debug_names=a.debug_names,
        )
        print(json.dumps(res))
        return 0
    except (ValueError, OSError, json.JSONDecodeError) as exc:
        print(json.dumps({'status': 'rejected', 'reason': str(exc)}), file=sys.stderr)
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
