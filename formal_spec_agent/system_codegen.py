"""Declarative multi-module C99 system composer (`fsa-system-v1`) on top of c99-lib-v1."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

from protocol_lab.codegen import Unsupported, integer
from protocol_lab.ir import load

from . import codegen_lib

HERE = Path(__file__).resolve().parent
SCHEMA = 'fsa-system-v1'


def _sha256(path: Path) -> str:
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def _sanitize_ident(text: str, upper: bool = False) -> str:
    ident = re.sub(r'[^A-Za-z0-9]+', '_', text).strip('_')
    if not ident:
        ident = 'x'
    if ident[0].isdigit():
        ident = 'm_' + ident
    return ident.upper() if upper else ident.lower()


def _load_modules(recipe: dict, recipe_dir: Path, byte_cap_default: int):
    modules = {}
    order = []
    raw_mods = recipe.get('modules', {})
    if type(raw_mods) is not dict or not raw_mods:
        raise ValueError('fsa-system-v1 requires non-empty modules mapping')
    for mid, cfg in raw_mods.items():
        if not re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*', mid):
            raise ValueError(f'Invalid module id: {mid}')
        mpath = (recipe_dir / cfg['model']).resolve()
        if not mpath.is_file():
            raise ValueError(f'Missing module model: {mpath}')
        actual_sha = _sha256(mpath)
        if 'sha256' in cfg and cfg['sha256'] != actual_sha:
            raise ValueError(f'Module {mid} sha256 mismatch')
        model = load(mpath)
        prefix = cfg.get('prefix', f'fsa_{mid}')
        cap = int(cfg.get('capacity', 1))
        if cap < 1:
            raise ValueError(f'Module {mid} capacity must be >= 1')
        bcap = int(cfg.get('byte_cap', byte_cap_default))
        acap = int(cfg.get('arena_cap', max(8192, bcap * 4)))
        free_state = cfg.get('free_state')
        if free_state is not None and free_state not in model['states']:
            raise ValueError(f'Module {mid} unknown free_state {free_state}')
        states = list(model['states'])
        events = list(model['events'])
        messages = list(model['messages'])
        scalar_vars = [n for n, v in model['variables'].items() if v['type'] != 'bytes']
        byte_vars = [n for n, v in model['variables'].items() if v['type'] == 'bytes']
        modules[mid] = {
            'id': mid,
            'model_rel': cfg['model'],
            'model_path': mpath,
            'sha256': actual_sha,
            'model': model,
            'prefix': prefix.lower(),
            'PREFIX': prefix.upper(),
            'capacity': cap,
            'byte_cap': bcap,
            'arena_cap': acap,
            'free_state': free_state,
            'states': states,
            'events': events,
            'messages': messages,
            'scalar_vars': scalar_vars,
            'byte_vars': byte_vars,
            'strings': codegen_lib.string_literals(model),
        }
        order.append(mid)
    return modules, order


def _ev_enum_sym(mod, ev_name: str) -> str:
    idx = mod['events'].index(ev_name)
    # Match codegen_lib unique_enum_names deterministically
    used = {}
    for i, name in enumerate(mod['events']):
        base = f"{mod['PREFIX']}_EV_{_sanitize_ident(name, upper=True)}"
        if base in used:
            base = f'{base}_{i}'
        used[base] = True
        if i == idx:
            return base
    raise AssertionError(ev_name)


def _state_enum_sym(mod, st_name: str) -> str:
    idx = mod['states'].index(st_name)
    used = {}
    for i, name in enumerate(mod['states']):
        base = f"{mod['PREFIX']}_STATE_{_sanitize_ident(name, upper=True)}"
        if base in used:
            base = f'{base}_{i}'
        used[base] = True
        if i == idx:
            return base
    raise AssertionError(st_name)


def _var_sym(mod, var_name: str):
    if var_name in mod['scalar_vars']:
        idx = mod['scalar_vars'].index(var_name)
        return ('scalar', idx, mod['model']['variables'][var_name]['type'])
    if var_name in mod['byte_vars']:
        idx = mod['byte_vars'].index(var_name)
        return ('bytes', idx, 'bytes')
    raise ValueError(f'Unknown var {var_name} in module {mod["id"]}')


def _field_idx(mod, msg_name: str, field_name: str):
    spec = mod['model']['messages'][msg_name]['fields']
    if field_name not in spec:
        raise ValueError(f'Unknown field {field_name} in {mod["id"]}.{msg_name}')
    return list(spec).index(field_name), spec[field_name]


def _render_arg_expr(arg_spec, src_mod, src_msg, src_slot_expr='it->src_slot',
                     item_expr='it->fields', mod_var_prefix='sys->m_'):
    if 'from_field' in arg_spec:
        fidx, _ = _field_idx(src_mod, src_msg, arg_spec['from_field'])
        return f'{item_expr}[{fidx}]'
    if arg_spec.get('from_source_slot'):
        return f'fsa_val_int((int64_t)({src_slot_expr}))'
    if 'from_source_var' in arg_spec:
        vname = arg_spec['from_source_var']
        kind, vidx, vtype = _var_sym(src_mod, vname)
        sm = f'(&{mod_var_prefix}{src_mod["id"]}[{src_slot_expr}])'
        if kind == 'bytes':
            return f'fsa_val_bytes({sm}->bdata[{vidx}], {sm}->blen[{vidx}])'
        if vtype == 'bool':
            return f'fsa_val_bool((int){sm}->v[{vidx}])'
        if vtype == 'seq32':
            return f'fsa_val_seq32((uint32_t){sm}->v[{vidx}])'
        return f'fsa_val_int({sm}->v[{vidx}])'
    if 'int' in arg_spec:
        return f'fsa_val_int({integer(int(arg_spec["int"]))})'
    if 'bool' in arg_spec:
        return f'fsa_val_bool({1 if arg_spec["bool"] else 0})'
    if 'seq32' in arg_spec:
        return f'fsa_val_seq32(UINT32_C({int(arg_spec["seq32"]) & 0xFFFFFFFF}))'
    if 'bytes' in arg_spec:
        vals = [int(x) & 0xFF for x in arg_spec['bytes']]
        if not vals:
            return 'fsa_val_bytes(NULL, 0U)'
        raw = ', '.join(str(x) for x in vals)
        return f'fsa_val_bytes((const uint8_t[]){{{raw}}}, {len(vals)}U)'
    if 'string_id' in arg_spec:
        return f'fsa_val_str_id({integer(int(arg_spec["string_id"]))})'
    raise ValueError(f'Unsupported arg_spec: {arg_spec!r}')


def render_system(recipe: dict, recipe_dir: Path, *, prefix: str = None, fast_dispatch: bool = True,
                  debug_names: bool = False):
    if recipe.get('schema') != SCHEMA:
        raise ValueError(f'Expected schema {SCHEMA}, got {recipe.get("schema")!r}')
    sys_name = prefix or recipe.get('system_name', 'fsa_system')
    if not re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*', sys_name):
        raise ValueError(f'Invalid system_name: {sys_name}')
    pfx = sys_name.lower()
    PFX = sys_name.upper()

    bus_q_cap = int(recipe.get('bus_queue_cap', 32))
    bus_b_cap = int(recipe.get('bus_byte_cap', 8192))
    byte_cap_default = int(recipe.get('byte_cap_default', 2048))
    modules, mod_order = _load_modules(recipe, recipe_dir, byte_cap_default)
    hooks = recipe.get('architecture_hooks') or {}
    host_outputs = list(recipe.get('host_outputs', []))
    routes = recipe.get('routes', {})
    entrypoints = list(recipe.get('entrypoints', []))

    # Compute max message fields across all modules for static bus storage
    max_msg_fields = 1
    max_arena = 1024
    max_bus_bytes_per_item = 1
    for m in modules.values():
        max_arena = max(max_arena, m['arena_cap'])
        for mspec in m['model']['messages'].values():
            fdict = mspec['fields']
            max_msg_fields = max(max_msg_fields, len(fdict))
            bcount = sum(1 for k in fdict.values() if k == 'bytes')
            if bcount > 0:
                max_bus_bytes_per_item = max(max_bus_bytes_per_item, bcount * min(m['byte_cap'], bus_b_cap))

    h = [
        f'/* Generated by Formal-Spec-Agent (system-codegen / {SCHEMA}) — do not edit manually. */',
        f'#ifndef {PFX}_SYSTEM_H',
        f'#define {PFX}_SYSTEM_H',
        '',
        '#include "fsa_lib_runtime.h"',
    ]
    for mid in mod_order:
        h.append(f'#include "{modules[mid]["prefix"]}.h"')
    h.extend([
        '',
        f'#define {PFX}_BUS_QUEUE_CAP {bus_q_cap}',
        f'#define {PFX}_BUS_MAX_FIELDS {max_msg_fields}',
        f'#define {PFX}_SHARED_ARENA_CAP {max_arena}U',
        f'#define {PFX}_BUS_ITEM_BYTES {max_bus_bytes_per_item}U',
        '',
        'enum {',
    ])
    for i, mid in enumerate(mod_order):
        h.append(f'    {PFX}_MOD_{_sanitize_ident(mid, upper=True)} = {i},')
    h.append(f'    {PFX}_NUM_MODULES = {len(mod_order)}')
    h.append('};')
    h.append('')

    if host_outputs:
        h.append('enum {')
        for i, oid in enumerate(host_outputs):
            h.append(f'    {PFX}_OUT_{_sanitize_ident(oid, upper=True)} = {i},')
        h.append(f'    {PFX}_NUM_HOST_OUTPUTS = {len(host_outputs)}')
        h.append('};')
        h.append('')

    h.extend([
        f'typedef void (*{pfx}_host_output_fn)(void *ctx, int out_id, uint16_t src_slot, '
        f'const fsa_val_t *fields, int nfields);',
        '',
        'typedef struct {',
        '    uint8_t src_mod;',
        '    uint16_t src_slot;',
        '    int msg_id;',
        '    int nfields;',
        f'    fsa_val_t fields[{PFX}_BUS_MAX_FIELDS];',
        f'    uint8_t byte_buf[{PFX}_BUS_ITEM_BYTES];',
        '    uint32_t byte_used;',
        f'}} {pfx}_bus_item_t;',
        '',
        'typedef union {',
    ])
    for mid in mod_order:
        h.append(f'    {modules[mid]["prefix"]}_machine_t {mid};')
    h.extend([
        f'}} {pfx}_saved_union_t;',
        '',
        f'typedef struct {pfx}_system {{',
    ])
    for mid in mod_order:
        mp = modules[mid]
        h.append(f'    {mp["prefix"]}_machine_t m_{mid}[{mp["capacity"]}];')
        h.append(f'    uint16_t evict_{mid};')
    h.extend([
        f'    {pfx}_bus_item_t bus[{PFX}_BUS_QUEUE_CAP];',
        '    uint16_t bus_head;',
        '    uint16_t bus_tail;',
        '    uint16_t bus_count;',
        '    uint8_t shared_arena_buf[' + f'{PFX}_SHARED_ARENA_CAP];',
        f'    {pfx}_saved_union_t shared_saved;',
        f'    {pfx}_host_output_fn on_output;',
        '    void *output_ctx;',
        '    int bus_overflow;',
        '    int initialized;',
        f'}} {pfx}_system_t;',
        '',
        f'int {pfx}_init({pfx}_system_t *sys, {pfx}_host_output_fn on_output, void *output_ctx);',
        f'int {pfx}_shutdown({pfx}_system_t *sys, int64_t now_ms);',
        f'int {pfx}_tick({pfx}_system_t *sys, int64_t now_ms);',
        f'int64_t {pfx}_next_due_ms(const {pfx}_system_t *sys);',
        '',
    ])

    for mid in mod_order:
        mp = modules[mid]
        h.append(f'int {pfx}_alloc_{mid}({pfx}_system_t *sys);')
        h.append(f'int {pfx}_get_{mid}_state(const {pfx}_system_t *sys, int slot);')
        h.append(f'int64_t {pfx}_get_{mid}_var_int(const {pfx}_system_t *sys, int slot, int var_idx);')
        if mp['byte_vars']:
            h.append(f'uint16_t {pfx}_get_{mid}_var_bytes(const {pfx}_system_t *sys, int slot, int bvar_idx, uint8_t *dst, uint16_t cap);')

    h.append('')
    for ep in entrypoints:
        ep_name = ep['name']
        params = [f'{pfx}_system_t *sys', 'int64_t now_ms']
        if ep.get('slot_mode', 'singleton') == 'slot_arg':
            params.append('int slot')
        for prm in ep.get('params', []):
            pt = prm['type']
            pn = prm['name']
            if pt == 'bytes':
                params.extend([f'const uint8_t *{pn}_ptr', f'uint16_t {pn}_len'])
            elif pt == 'bool':
                params.append(f'int {pn}')
            elif pt == 'seq32':
                params.append(f'uint32_t {pn}')
            elif pt == 'string':
                params.append(f'int64_t {pn}')
            else:
                params.append(f'int64_t {pn}')
        h.append(f'int {pfx}_{ep_name}({", ".join(params)});')
    h.extend(['', f'#endif /* {PFX}_SYSTEM_H */', ''])

    # Build C source
    c = [
        f'/* Generated by Formal-Spec-Agent (system-codegen / {SCHEMA}) — do not edit manually. */',
        f'#include "{pfx}.h"',
        '',
        f'typedef struct {{',
        f'    {pfx}_system_t *sys;',
        '    uint8_t src_mod;',
        '    uint16_t src_slot;',
        f'}} {pfx}_emit_ctx_t;',
        '',
        f'static void {pfx}_on_mod_emit(void *raw_ctx, int msg_id, const fsa_val_t *fields, int nfields) {{',
        f'    {pfx}_emit_ctx_t *ec = ({pfx}_emit_ctx_t *)raw_ctx;',
        f'    {pfx}_system_t *sys = ec->sys;',
        f'    if (!sys || sys->bus_count >= {PFX}_BUS_QUEUE_CAP || nfields < 0 || nfields > {PFX}_BUS_MAX_FIELDS) {{',
        '        if (sys) sys->bus_overflow = 1;',
        '        return;',
        '    }',
        f'    {pfx}_bus_item_t *it = &sys->bus[sys->bus_tail];',
        '    memset(it, 0, sizeof(*it));',
        '    it->src_mod = ec->src_mod;',
        '    it->src_slot = ec->src_slot;',
        '    it->msg_id = msg_id;',
        '    it->nfields = nfields;',
        '    it->byte_used = 0U;',
        '    for (int i = 0; i < nfields; i++) {',
        '        it->fields[i] = fields[i];',
        '        if (fields[i].kind == FSA_KIND_BYTES && fields[i].bytes.len > 0U && fields[i].bytes.ptr) {',
        f'            if (it->byte_used + (uint32_t)fields[i].bytes.len > (uint32_t){PFX}_BUS_ITEM_BYTES) {{',
        '                sys->bus_overflow = 1;',
        '                return;',
        '            }',
        '            uint8_t *dst = it->byte_buf + it->byte_used;',
        '            memcpy(dst, fields[i].bytes.ptr, fields[i].bytes.len);',
        '            it->fields[i].bytes.ptr = dst;',
        '            it->byte_used += (uint32_t)fields[i].bytes.len;',
        '        }',
        '    }',
        f'    sys->bus_tail = (uint16_t)((sys->bus_tail + 1U) % (uint16_t){PFX}_BUS_QUEUE_CAP);',
        '    sys->bus_count++;',
        '}',
        '',
    ]

    # Step wrapper per module using shared arena + shared saved union
    for mid in mod_order:
        mp = modules[mid]
        mod_enum = f'{PFX}_MOD_{_sanitize_ident(mid, upper=True)}'
        c.extend([
            f'static int {pfx}_step_{mid}({pfx}_system_t *sys, int slot, int64_t now_ms, int event, '
            f'const fsa_val_t *args, int nargs) {{',
            f'    if (!sys || slot < 0 || slot >= {mp["capacity"]}) return -FSA_ERR_INVALID_ARG;',
            f'    fsa_arena_t arena = {{ sys->shared_arena_buf, 0U, (uint32_t){PFX}_SHARED_ARENA_CAP }};',
            f'    {pfx}_emit_ctx_t ec = {{ sys, (uint8_t){mod_enum}, (uint16_t)slot }};',
            f'    return {mp["prefix"]}_step_ws(&sys->m_{mid}[slot], now_ms, event, args, nargs, '
            f'{pfx}_on_mod_emit, &ec, &arena, &sys->shared_saved.{mid}, NULL);',
            '}',
            '',
        ])

    # Helper emitters for single route / lookup attempt
    def emit_when_check(when_list, src_mod, src_msg, fail_stmt, indent='        '):
        if not when_list:
            return
        conds = []
        for w in when_list:
            fidx, _ = _field_idx(src_mod, src_msg, w['field'])
            if 'int' in w:
                conds.append(f'(it->fields[{fidx}].i64 == {integer(int(w["int"]))})')
            elif 'bool' in w:
                conds.append(f'(it->fields[{fidx}].i64 == {1 if w["bool"] else 0})')
            else:
                raise ValueError(f'Unsupported when_field_eq: {w}')
        c.append(f'{indent}if (!({" && ".join(conds)})) {fail_stmt}')

    def emit_match_loop(step_cfg, src_mod, src_msg, mode, matched_flag_var, indent='            '):
        tmid = step_cfg['target']
        tmod = modules[tmid]
        tcap = tmod['capacity']
        ev_sym = _ev_enum_sym(tmod, step_cfg['event'])
        args_spec = step_cfg.get('args', [])
        c.append(f'{indent}{{')
        emit_when_check(step_cfg.get('when_field_eq'), src_mod, src_msg, 'goto skip_attempt;', indent + '    ')
        c.append(f'{indent}    int target_slot = -1;')
        c.append(f'{indent}    for (int i = 0; i < {tcap}; i++) {{')
        c.append(f'{indent}        const {tmod["prefix"]}_machine_t *cand = &sys->m_{tmid}[i];')
        if step_cfg.get('in_states'):
            st_cond = ' || '.join(f'cand->state == {_state_enum_sym(tmod, s)}' for s in step_cfg['in_states'])
            c.append(f'{indent}        if (!({st_cond})) continue;')
        if step_cfg.get('not_in_states'):
            st_cond = ' || '.join(f'cand->state == {_state_enum_sym(tmod, s)}' for s in step_cfg['not_in_states'])
            c.append(f'{indent}        if ({st_cond}) continue;')
        if mode == 'upsert' and tmod['free_state'] is not None and not step_cfg.get('not_in_states'):
            c.append(f'{indent}        if (cand->state == {_state_enum_sym(tmod, tmod["free_state"])}) continue;')
        for mv in step_cfg.get('match_vars', []):
            vkind, vidx, _ = _var_sym(tmod, mv['var'])
            fidx, _ = _field_idx(src_mod, src_msg, mv['from_field'])
            wild = bool(mv.get('wildcard_empty_or_zero', False))
            if vkind == 'bytes':
                eq_b = (f'(cand->blen[{vidx}] == it->fields[{fidx}].bytes.len && '
                        f'(cand->blen[{vidx}] == 0U || memcmp(cand->bdata[{vidx}], it->fields[{fidx}].bytes.ptr, cand->blen[{vidx}]) == 0))')
                if wild:
                    c.append(f'{indent}        if (!(cand->blen[{vidx}] == 0U || {eq_b})) continue;')
                else:
                    c.append(f'{indent}        if (!{eq_b}) continue;')
            else:
                if wild:
                    c.append(f'{indent}        if (!(cand->v[{vidx}] == 0 || cand->v[{vidx}] == it->fields[{fidx}].i64)) continue;')
                else:
                    c.append(f'{indent}        if (cand->v[{vidx}] != it->fields[{fidx}].i64) continue;')
        c.append(f'{indent}        target_slot = i; break;')
        c.append(f'{indent}    }}')

        if mode == 'upsert':
            if tmod['free_state'] is None:
                raise ValueError(f'upsert requires free_state on {tmid}')
            fst = _state_enum_sym(tmod, tmod['free_state'])
            c.append(f'{indent}    if (target_slot < 0) {{')
            c.append(f'{indent}        for (int i = 0; i < {tcap}; i++) {{')
            c.append(f'{indent}            if (sys->m_{tmid}[i].state == {fst}) {{ target_slot = i; break; }}')
            c.append(f'{indent}        }}')
            c.append(f'{indent}        if (target_slot < 0) {{')
            c.append(f'{indent}            target_slot = (int)(sys->evict_{tmid} % (uint16_t){tcap});')
            c.append(f'{indent}            sys->evict_{tmid}++;')
            c.append(f'{indent}            {tmod["prefix"]}_init(&sys->m_{tmid}[target_slot]);')
            c.append(f'{indent}        }}')
            c.append(f'{indent}    }}')

        if mode == 'fork_from_match':
            if tmod['free_state'] is None:
                raise ValueError(f'fork_from_match requires free_state on {tmid}')
            fst = _state_enum_sym(tmod, tmod['free_state'])
            c.append(f'{indent}    if (target_slot >= 0) {{')
            c.append(f'{indent}        int child = -1;')
            c.append(f'{indent}        for (int i = 0; i < {tcap}; i++) {{')
            c.append(f'{indent}            if (sys->m_{tmid}[i].state == {fst}) {{ child = i; break; }}')
            c.append(f'{indent}        }}')
            c.append(f'{indent}        if (child >= 0) {{')
            c.append(f'{indent}            {tmod["prefix"]}_init(&sys->m_{tmid}[child]);')
            for cv in step_cfg.get('copy_vars', []):
                ckind, cidx, _ = _var_sym(tmod, cv)
                if ckind == 'bytes':
                    c.append(f'{indent}            sys->m_{tmid}[child].blen[{cidx}] = sys->m_{tmid}[target_slot].blen[{cidx}];')
                    c.append(f'{indent}            if (sys->m_{tmid}[child].blen[{cidx}] > 0U) {{')
                    c.append(f'{indent}                memcpy(sys->m_{tmid}[child].bdata[{cidx}], sys->m_{tmid}[target_slot].bdata[{cidx}], sys->m_{tmid}[child].blen[{cidx}]);')
                    c.append(f'{indent}            }}')
                else:
                    c.append(f'{indent}            sys->m_{tmid}[child].v[{cidx}] = sys->m_{tmid}[target_slot].v[{cidx}];')
            if step_cfg.get('parent_slot_var'):
                _, pvi, _ = _var_sym(tmod, step_cfg['parent_slot_var'])
                c.append(f'{indent}            sys->m_{tmid}[child].v[{pvi}] = (int64_t)target_slot;')
            c.append(f'{indent}            target_slot = child;')
            c.append(f'{indent}        }} else {{')
            c.append(f'{indent}            target_slot = -1;')
            c.append(f'{indent}            {matched_flag_var} = 1;')
            c.append(f'{indent}        }}')
            c.append(f'{indent}    }}')

        c.append(f'{indent}    if (target_slot >= 0) {{')
        if args_spec:
            rendered = [_render_arg_expr(a, src_mod, src_msg) for a in args_spec]
            c.append(f'{indent}        fsa_val_t rargs[{len(args_spec)}] = {{ {", ".join(rendered)} }};')
            c.append(f'{indent}        (void){pfx}_step_{tmid}(sys, target_slot, now_ms, {ev_sym}, rargs, {len(args_spec)});')
        else:
            c.append(f'{indent}        (void){pfx}_step_{tmid}(sys, target_slot, now_ms, {ev_sym}, NULL, 0);')
        c.append(f'{indent}        {matched_flag_var} = 1;')
        c.append(f'{indent}    }}')
        if step_cfg.get('when_field_eq'):
            c.append(f'{indent}skip_attempt: (void)0;')
        c.append(f'{indent}}}')

    def emit_single_route(route, src_mod, src_msg, indent='        '):
        rk = route['kind']
        if rk == 'host_out':
            oid = f'{PFX}_OUT_{_sanitize_ident(route["out_id"], upper=True)}'
            c.append(f'{indent}{{')
            if route.get('when_field_eq'):
                emit_when_check(route['when_field_eq'], src_mod, src_msg, 'goto skip_host_out;', indent + '    ')
            if route.get('fields'):
                rendered = [_render_arg_expr(a, src_mod, src_msg) for a in route['fields']]
                c.append(f'{indent}    fsa_val_t hargs[{len(rendered)}] = {{ {", ".join(rendered)} }};')
                c.append(f'{indent}    if (sys->on_output) sys->on_output(sys->output_ctx, {oid}, it->src_slot, hargs, {len(rendered)});')
            else:
                c.append(f'{indent}    if (sys->on_output) sys->on_output(sys->output_ctx, {oid}, it->src_slot, it->fields, it->nfields);')
            if route.get('when_field_eq'):
                c.append(f'{indent}skip_host_out: (void)0;')
            c.append(f'{indent}}}')
        elif rk in ('singleton', 'slot_index'):
            tmid = route['target']
            tmod = modules[tmid]
            ev_sym = _ev_enum_sym(tmod, route['event'])
            args_spec = route.get('args', [])
            slot_expr = '0' if rk == 'singleton' else _render_arg_expr(route['slot'], src_mod, src_msg) + '.i64'
            c.append(f'{indent}{{')
            if route.get('when_field_eq'):
                emit_when_check(route['when_field_eq'], src_mod, src_msg, 'goto skip_route;', indent + '    ')
            if args_spec:
                rendered = [_render_arg_expr(a, src_mod, src_msg) for a in args_spec]
                c.append(f'{indent}    fsa_val_t rargs[{len(args_spec)}] = {{ {", ".join(rendered)} }};')
                c.append(f'{indent}    (void){pfx}_step_{tmid}(sys, (int)({slot_expr}), now_ms, {ev_sym}, rargs, {len(args_spec)});')
            else:
                c.append(f'{indent}    (void){pfx}_step_{tmid}(sys, (int)({slot_expr}), now_ms, {ev_sym}, NULL, 0);')
            if route.get('when_field_eq'):
                c.append(f'{indent}skip_route: (void)0;')
            c.append(f'{indent}}}')
        elif rk in ('match', 'upsert', 'fork_from_match'):
            c.append(f'{indent}{{')
            c.append(f'{indent}    int matched = 0;')
            emit_match_loop(route, src_mod, src_msg, rk, 'matched', indent + '    ')
            if route.get('on_miss'):
                c.append(f'{indent}    if (!matched) {{')
                emit_single_route(route['on_miss'], src_mod, src_msg, indent + '        ')
                c.append(f'{indent}    }}')
            else:
                c.append(f'{indent}    (void)matched;')
            c.append(f'{indent}}}')
        elif rk == 'lookup_chain':
            c.append(f'{indent}{{')
            c.append(f'{indent}    int matched = 0;')
            for att in route.get('attempts', []):
                ak = att['kind']
                if ak not in ('match', 'fork_from_match', 'upsert'):
                    raise ValueError(f'Unsupported lookup_chain attempt kind: {ak}')
                c.append(f'{indent}    if (!matched) {{')
                emit_match_loop(att, src_mod, src_msg, ak, 'matched', indent + '        ')
                c.append(f'{indent}    }}')
            if route.get('on_miss'):
                c.append(f'{indent}    if (!matched) {{')
                emit_single_route(route['on_miss'], src_mod, src_msg, indent + '        ')
                c.append(f'{indent}    }}')
            else:
                c.append(f'{indent}    (void)matched;')
            c.append(f'{indent}}}')
        else:
            raise ValueError(f'Unsupported route kind: {rk}')

    # Emit drain_bus
    c.extend([
        f'static void {pfx}_drain_bus({pfx}_system_t *sys, int64_t now_ms) {{',
        '    while (sys->bus_count > 0U) {',
        f'        const {pfx}_bus_item_t *it = &sys->bus[sys->bus_head];',
        f'        sys->bus_head = (uint16_t)((sys->bus_head + 1U) % (uint16_t){PFX}_BUS_QUEUE_CAP);',
        '        sys->bus_count--;',
        '        switch (it->src_mod) {',
    ])
    for mid in mod_order:
        mp = modules[mid]
        mod_enum = f'{PFX}_MOD_{_sanitize_ident(mid, upper=True)}'
        mod_routes = []
        for rkey, rval in routes.items():
            rmod, rmsg = rkey.split('.', 1)
            if rmod == mid:
                rlist = rval if isinstance(rval, list) else [rval]
                mod_routes.append((rmsg, rlist))
        if not mod_routes:
            continue
        c.append(f'            case {mod_enum}: {{')
        c.append('                switch (it->msg_id) {')
        for rmsg, rlist in mod_routes:
            mid_idx = mp['messages'].index(rmsg)
            c.append(f'                    case {mid_idx}: {{')
            for r in rlist:
                emit_single_route(r, mp, rmsg, '                        ')
            c.append('                        break;')
            c.append('                    }')
        c.append('                    default: break;')
        c.append('                }')
        c.append('                break;')
        c.append('            }')
    c.extend([
        '            default: break;',
        '        }',
        '    }',
        '}',
        '',
    ])

    # Architecture hook helpers
    def emit_hook(kind, now_expr, indent='    '):
        if not hooks:
            return
        if kind == 'start':
            if hooks.get('port'):
                pm = hooks['port']
                c.append(f'{indent}(void){pfx}_step_{pm}(sys, 0, {now_expr}, {_ev_enum_sym(modules[pm], hooks["port_start_ev"])}, NULL, 0);')
            if hooks.get('actor') and hooks.get('actor_start_ev'):
                am = hooks['actor']
                c.append(f'{indent}(void){pfx}_step_{am}(sys, 0, {now_expr}, {_ev_enum_sym(modules[am], hooks["actor_start_ev"])}, NULL, 0);')
        elif kind == 'stop':
            if hooks.get('actor') and hooks.get('actor_stop_ev'):
                am = hooks['actor']
                c.append(f'{indent}(void){pfx}_step_{am}(sys, 0, {now_expr}, {_ev_enum_sym(modules[am], hooks["actor_stop_ev"])}, NULL, 0);')
            if hooks.get('port') and hooks.get('port_stop_ev'):
                pm = hooks['port']
                c.append(f'{indent}(void){pfx}_step_{pm}(sys, 0, {now_expr}, {_ev_enum_sym(modules[pm], hooks["port_stop_ev"])}, NULL, 0);')
        elif kind == 'rx_begin' and hooks.get('actor') and hooks.get('actor_post_rx_ev'):
            am = hooks['actor']
            c.append(f'{indent}(void){pfx}_step_{am}(sys, 0, {now_expr}, {_ev_enum_sym(modules[am], hooks["actor_post_rx_ev"])}, NULL, 0);')
            if hooks.get('actor_dispatch_ev'):
                c.append(f'{indent}(void){pfx}_step_{am}(sys, 0, {now_expr}, {_ev_enum_sym(modules[am], hooks["actor_dispatch_ev"])}, NULL, 0);')
        elif kind == 'api_begin' and hooks.get('actor') and hooks.get('actor_post_api_ev'):
            am = hooks['actor']
            c.append(f'{indent}(void){pfx}_step_{am}(sys, 0, {now_expr}, {_ev_enum_sym(modules[am], hooks["actor_post_api_ev"])}, NULL, 0);')
            if hooks.get('actor_dispatch_ev'):
                c.append(f'{indent}(void){pfx}_step_{am}(sys, 0, {now_expr}, {_ev_enum_sym(modules[am], hooks["actor_dispatch_ev"])}, NULL, 0);')
        elif kind == 'tick_begin' and hooks.get('actor') and hooks.get('actor_dispatch_ev'):
            am = hooks['actor']
            c.append(f'{indent}(void){pfx}_step_{am}(sys, 0, {now_expr}, {_ev_enum_sym(modules[am], hooks["actor_dispatch_ev"])}, NULL, 0);')
        elif kind == 'end' and hooks.get('actor') and hooks.get('actor_complete_ev'):
            am = hooks['actor']
            c.append(f'{indent}(void){pfx}_step_{am}(sys, 0, {now_expr}, {_ev_enum_sym(modules[am], hooks["actor_complete_ev"])}, NULL, 0);')

    # init / shutdown / tick / next_due_ms
    c.extend([
        f'int {pfx}_init({pfx}_system_t *sys, {pfx}_host_output_fn on_output, void *output_ctx) {{',
        '    if (!sys) return -FSA_ERR_INVALID_ARG;',
        '    memset(sys, 0, sizeof(*sys));',
        '    sys->on_output = on_output;',
        '    sys->output_ctx = output_ctx;',
    ])
    for mid in mod_order:
        mp = modules[mid]
        c.append(f'    for (int i = 0; i < {mp["capacity"]}; i++) {{')
        c.append(f'        int rc = {mp["prefix"]}_init(&sys->m_{mid}[i]);')
        c.append('        if (rc != FSA_OK) return rc;')
        c.append('    }')
    emit_hook('start', '0')
    c.extend([
        f'    {pfx}_drain_bus(sys, 0);',
        '    sys->initialized = 1;',
        '    return FSA_OK;',
        '}',
        '',
        f'int {pfx}_shutdown({pfx}_system_t *sys, int64_t now_ms) {{',
        '    if (!sys || !sys->initialized) return -FSA_ERR_INVALID_ARG;',
    ])
    emit_hook('stop', 'now_ms')
    c.extend([
        f'    {pfx}_drain_bus(sys, now_ms);',
        '    sys->initialized = 0;',
        '    return FSA_OK;',
        '}',
        '',
        f'int64_t {pfx}_next_due_ms(const {pfx}_system_t *sys) {{',
        '    if (!sys) return -1;',
        '    int64_t best = -1;',
    ])
    for mid in mod_order:
        mp = modules[mid]
        if not mp['model']['timers']:
            continue
        c.append(f'    for (int i = 0; i < {mp["capacity"]}; i++) {{')
        c.append(f'        int64_t d = {mp["prefix"]}_next_due_ms(&sys->m_{mid}[i]);')
        c.append('        if (d >= 0 && (best < 0 || d < best)) best = d;')
        c.append('    }')
    c.extend([
        '    return best;',
        '}',
        '',
        f'int {pfx}_tick({pfx}_system_t *sys, int64_t now_ms) {{',
        '    if (!sys) return -FSA_ERR_INVALID_ARG;',
    ])
    emit_hook('tick_begin', 'now_ms')
    c.extend([
        '    int steps = 0;',
        '    for (;;) {',
        '        int progressed = 0;',
    ])
    for mid in mod_order:
        mp = modules[mid]
        if not mp['model']['timers']:
            continue
        mod_enum = f'{PFX}_MOD_{_sanitize_ident(mid, upper=True)}'
        c.append(f'        for (int i = 0; i < {mp["capacity"]}; i++) {{')
        c.append(f'            int64_t d = {mp["prefix"]}_next_due_ms(&sys->m_{mid}[i]);')
        c.append('            if (d >= 0 && d <= now_ms) {')
        c.append(f'                fsa_arena_t arena = {{ sys->shared_arena_buf, 0U, (uint32_t){PFX}_SHARED_ARENA_CAP }};')
        c.append(f'                {pfx}_emit_ctx_t ec = {{ sys, (uint8_t){mod_enum}, (uint16_t)i }};')
        c.append(f'                int rc = {mp["prefix"]}_tick_one_ws(&sys->m_{mid}[i], now_ms, {pfx}_on_mod_emit, &ec, &arena, &sys->shared_saved.{mid}, NULL);')
        c.append('                if (rc < 0) return rc;')
        c.append('                if (rc > 0) { progressed = 1; steps++; }')
        c.append('            }')
        c.append('        }')
    c.extend([
        f'        {pfx}_drain_bus(sys, now_ms);',
        '        if (!progressed || steps >= 4096) break;',
        '    }',
    ])
    emit_hook('end', 'now_ms')
    c.extend([
        '    return FSA_OK;',
        '}',
        '',
    ])

    # Slot allocators and read-only getters
    for mid in mod_order:
        mp = modules[mid]
        c.append(f'int {pfx}_alloc_{mid}({pfx}_system_t *sys) {{')
        if mp['free_state'] is not None:
            fst = _state_enum_sym(mp, mp['free_state'])
            c.append('    if (!sys) return -1;')
            c.append(f'    for (int i = 0; i < {mp["capacity"]}; i++) {{')
            c.append(f'        if (sys->m_{mid}[i].state == {fst}) return i;')
            c.append('    }')
            c.append('    return -1;')
        else:
            c.append('    (void)sys; return 0;')
        c.append('}')
        c.append(f'int {pfx}_get_{mid}_state(const {pfx}_system_t *sys, int slot) {{')
        c.append(f'    if (!sys || slot < 0 || slot >= {mp["capacity"]}) return -1;')
        c.append(f'    return sys->m_{mid}[slot].state;')
        c.append('}')
        c.append(f'int64_t {pfx}_get_{mid}_var_int(const {pfx}_system_t *sys, int slot, int var_idx) {{')
        c.append(f'    if (!sys || slot < 0 || slot >= {mp["capacity"]} || var_idx < 0 || var_idx >= {mp["prefix"].upper()}_NUM_SCALAR_VARS) return 0;')
        c.append(f'    return sys->m_{mid}[slot].v[var_idx];')
        c.append('}')
        if mp['byte_vars']:
            c.append(f'uint16_t {pfx}_get_{mid}_var_bytes(const {pfx}_system_t *sys, int slot, int bvar_idx, uint8_t *dst, uint16_t cap) {{')
            c.append(f'    if (!sys || slot < 0 || slot >= {mp["capacity"]} || bvar_idx < 0 || bvar_idx >= {mp["prefix"].upper()}_NUM_BYTE_VARS) return 0U;')
            c.append(f'    uint16_t len = sys->m_{mid}[slot].blen[bvar_idx];')
            c.append('    uint16_t n = len < cap ? len : cap;')
            c.append(f'    if (dst && n > 0U) memcpy(dst, sys->m_{mid}[slot].bdata[bvar_idx], n);')
            c.append('    return n;')
            c.append('}')
        c.append('')

    # Entrypoints
    for ep in entrypoints:
        ep_name = ep['name']
        tmid = ep['target']
        tmod = modules[tmid]
        ev_sym = _ev_enum_sym(tmod, ep['event'])
        slot_mode = ep.get('slot_mode', 'singleton')
        params = [f'{pfx}_system_t *sys', 'int64_t now_ms']
        if slot_mode == 'slot_arg':
            params.append('int slot')
        arg_vals = []
        for prm in ep.get('params', []):
            pt = prm['type']
            pn = prm['name']
            if pt == 'bytes':
                params.extend([f'const uint8_t *{pn}_ptr', f'uint16_t {pn}_len'])
                arg_vals.append(f'fsa_val_bytes({pn}_ptr, {pn}_len)')
            elif pt == 'bool':
                params.append(f'int {pn}')
                arg_vals.append(f'fsa_val_bool({pn})')
            elif pt == 'seq32':
                params.append(f'uint32_t {pn}')
                arg_vals.append(f'fsa_val_seq32({pn})')
            elif pt == 'string':
                params.append(f'int64_t {pn}')
                arg_vals.append(f'fsa_val_str_id({pn})')
            else:
                params.append(f'int64_t {pn}')
                arg_vals.append(f'fsa_val_int({pn})')

        c.append(f'int {pfx}_{ep_name}({", ".join(params)}) {{')
        c.append('    if (!sys) return -FSA_ERR_INVALID_ARG;')
        slot_expr = 'slot' if slot_mode == 'slot_arg' else '0'
        if ep.get('is_rx'):
            emit_hook('rx_begin', 'now_ms')
        elif ep.get('is_api'):
            emit_hook('api_begin', 'now_ms')
        if arg_vals:
            c.append(f'    fsa_val_t args[{len(arg_vals)}] = {{ {", ".join(arg_vals)} }};')
            c.append(f'    int rc = {pfx}_step_{tmid}(sys, {slot_expr}, now_ms, {ev_sym}, args, {len(arg_vals)});')
        else:
            c.append(f'    int rc = {pfx}_step_{tmid}(sys, {slot_expr}, now_ms, {ev_sym}, NULL, 0);')
        c.append(f'    if (rc == FSA_OK) {pfx}_drain_bus(sys, now_ms);')
        if ep.get('is_rx') or ep.get('is_api'):
            emit_hook('end', 'now_ms')
        c.append('    return rc;')
        c.append('}')
        c.append('')

    return '\n'.join(h), '\n'.join(c), modules, mod_order


def generate_system(recipe_file, out_dir, *, prefix=None, fast_dispatch=True, debug_names=False):
    recipe_file = Path(recipe_file).resolve()
    out_dir = Path(out_dir).resolve()
    if out_dir.exists():
        raise ValueError(f'Fresh output directory required: {out_dir}')
    recipe = json.loads(recipe_file.read_text(encoding='utf-8'))
    sys_pfx = (prefix or recipe.get('system_name', 'fsa_system')).lower()
    h_text, c_text, modules, mod_order = render_system(
        recipe, recipe_file.parent, prefix=sys_pfx,
        fast_dispatch=fast_dispatch, debug_names=debug_names,
    )
    out_dir.mkdir(parents=True, exist_ok=True)

    outputs = {}
    rt_bytes = (HERE / 'codegen_lib_runtime.h').read_bytes()
    (out_dir / 'fsa_lib_runtime.h').write_bytes(rt_bytes)
    outputs['fsa_lib_runtime.h'] = _sha256(out_dir / 'fsa_lib_runtime.h')

    mod_meta = {}
    for mid in mod_order:
        mp = modules[mid]
        mh, mc, meta = codegen_lib.render(
            mp['model'], prefix=mp['prefix'], byte_cap=mp['byte_cap'],
            arena_cap=mp['arena_cap'], fast_dispatch=fast_dispatch, debug_names=debug_names,
        )
        (out_dir / f'{mp["prefix"]}.h').write_text(mh, encoding='utf-8')
        (out_dir / f'{mp["prefix"]}.c').write_text(mc, encoding='utf-8')
        outputs[f'{mp["prefix"]}.h'] = _sha256(out_dir / f'{mp["prefix"]}.h')
        outputs[f'{mp["prefix"]}.c'] = _sha256(out_dir / f'{mp["prefix"]}.c')
        mod_meta[mid] = {
            'model': mp['model_rel'],
            'model_sha256': mp['sha256'],
            'prefix': mp['prefix'],
            'capacity': mp['capacity'],
            'rules': meta['rules'],
            'shared_helpers': meta['shared_helpers'],
        }

    (out_dir / f'{sys_pfx}.h').write_text(h_text, encoding='utf-8')
    (out_dir / f'{sys_pfx}.c').write_text(c_text, encoding='utf-8')
    outputs[f'{sys_pfx}.h'] = _sha256(out_dir / f'{sys_pfx}.h')
    outputs[f'{sys_pfx}.c'] = _sha256(out_dir / f'{sys_pfx}.c')

    manifest = {
        'schema': SCHEMA,
        'system_prefix': sys_pfx,
        'recipe': str(recipe_file.name),
        'recipe_sha256': _sha256(recipe_file),
        'fast_dispatch': bool(fast_dispatch),
        'modules': mod_meta,
        'outputs': outputs,
    }
    (out_dir / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n', encoding='utf-8')
    return manifest


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('recipe', type=Path)
    p.add_argument('--out', type=Path, required=True)
    p.add_argument('--prefix', default=None)
    grp = p.add_mutually_exclusive_group()
    grp.add_argument('--fast-dispatch', action='store_true')
    grp.add_argument('--strict-dispatch', action='store_true')
    p.add_argument('--debug-names', action='store_true')
    a = p.parse_args(argv)
    fast = not a.strict_dispatch
    try:
        res = generate_system(
            a.recipe, a.out, prefix=a.prefix,
            fast_dispatch=fast, debug_names=a.debug_names,
        )
        print(json.dumps(res))
        return 0
    except (ValueError, OSError, json.JSONDecodeError, Unsupported) as exc:
        print(json.dumps({'status': 'rejected', 'reason': str(exc)}), file=sys.stderr)
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
