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
           fast_dispatch=False, debug_names=False, shared_runtime=False):
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
        ast_sizes = {}
        size_memo = {}
        reps = {}
        shared = {}
        shared_bodies = {}
        planning = True

        def node_size(node):
            nid = id(node)
            if nid in size_memo:
                return size_memo[nid]
            if isinstance(node, dict) and 'args' in node:
                sz = 1 + sum(node_size(a) for a in node['args'])
            else:
                sz = 1
            size_memo[nid] = sz
            return sz

        def raw_concat_leaves(node):
            if isinstance(node, dict) and node.get('op') == 'bytes_concat':
                return raw_concat_leaves(node['args'][0]) + raw_concat_leaves(node['args'][1])
            return [node]

        def is_leaf_expr(node):
            return not (isinstance(node, dict) and 'op' in node)

        def match_u16be_raw(node):
            if not (isinstance(node, dict) and node.get('op') == 'add'):
                return None
            lhs, rhs = node['args']
            if not (isinstance(lhs, dict) and lhs.get('op') == 'mul' and type(lhs['args'][1]) is int and lhs['args'][1] == 256):
                return None
            at0 = lhs['args'][0]
            if not (isinstance(at0, dict) and at0.get('op') == 'bytes_at_or_zero'):
                return None
            if not (isinstance(rhs, dict) and rhs.get('op') == 'bytes_at_or_zero'):
                return None
            buf0, off0 = at0['args']
            buf1, off1 = rhs['args']
            if buf0 != buf1 or not (is_leaf_expr(buf0) or is_leaf_expr(off0)):
                return None
            if type(off0) is int and type(off1) is int and off1 == off0 + 1:
                return (buf0, off0)
            if isinstance(off0, dict) and off1 == {'op': 'add', 'args': [off0, 1]}:
                return (buf0, off0)
            return None

        def match_u32be_raw(node):
            if not (isinstance(node, dict) and node.get('op') == 'add'):
                return None
            lhs, rhs = node['args']
            if not (isinstance(lhs, dict) and lhs.get('op') == 'mul' and type(lhs['args'][1]) is int and lhs['args'][1] == 65536):
                return None
            hi = match_u16be_raw(lhs['args'][0])
            lo = match_u16be_raw(rhs)
            if not hi or not lo or hi[0] != lo[0]:
                return None
            buf0, off0 = hi
            _, off2 = lo
            if type(off0) is int and type(off2) is int and off2 == off0 + 2:
                return (buf0, off0)
            if isinstance(off0, dict) and off2 == {'op': 'add', 'args': [off0, 2]}:
                return (buf0, off0)
            return None

        def render_concat_leaves(leaves, event):
            if len(leaves) == 2:
                return f'fsa_concat(arena, {render_expr(leaves[0], event)}, {render_expr(leaves[1], event)}, {PFX}_BYTE_CAP, err)'
            if len(leaves) == 3:
                return f'fsa_concat3(arena, {render_expr(leaves[0], event)}, {render_expr(leaves[1], event)}, {render_expr(leaves[2], event)}, {PFX}_BYTE_CAP, err)'
            if len(leaves) == 4:
                return f'fsa_concat4(arena, {render_expr(leaves[0], event)}, {render_expr(leaves[1], event)}, {render_expr(leaves[2], event)}, {render_expr(leaves[3], event)}, {PFX}_BYTE_CAP, err)'
            acc = render_concat_leaves(leaves[:4], event)
            idx = 4
            while idx < len(leaves):
                rem = len(leaves) - idx
                if rem == 1:
                    acc = f'fsa_concat(arena, {acc}, {render_expr(leaves[idx], event)}, {PFX}_BYTE_CAP, err)'
                    idx += 1
                elif rem == 2:
                    acc = f'fsa_concat3(arena, {acc}, {render_expr(leaves[idx], event)}, {render_expr(leaves[idx + 1], event)}, {PFX}_BYTE_CAP, err)'
                    idx += 2
                else:
                    acc = f'fsa_concat4(arena, {acc}, {render_expr(leaves[idx], event)}, {render_expr(leaves[idx + 1], event)}, {render_expr(leaves[idx + 2], event)}, {PFX}_BYTE_CAP, err)'
                    idx += 3
            return acc

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

            op = e['op']
            if op == 'bytes_concat':
                leaves = raw_concat_leaves(e)
                non_empty = [
                    lf for lf in leaves
                    if not (isinstance(lf, dict) and 'bytes' in lf and len(lf['bytes']) == 0)
                ]
                if len(non_empty) == 0:
                    return 'fsa_slice_make(NULL, 0U)'
                if len(non_empty) == 1 and isinstance(non_empty[0], dict) and ('var' in non_empty[0] or 'bytes' in non_empty[0]):
                    return render_expr(non_empty[0], event)
                if len(non_empty) >= 2:
                    return render_concat_leaves(non_empty, event)
                return render_concat_leaves(leaves, event)
            if op == 'add':
                m32 = match_u32be_raw(e)
                if m32 is not None:
                    return f'fsa_read_u32be({render_expr(m32[0], event)}, {render_expr(m32[1], event)}, {PFX}_BYTE_CAP, err)'
                m16 = match_u16be_raw(e)
                if m16 is not None:
                    return f'fsa_read_u16be({render_expr(m16[0], event)}, {render_expr(m16[1], event)}, {PFX}_BYTE_CAP, err)'
            args = [render_expr(x, event) for x in e['args']]
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
                ast_sizes.setdefault(key, node_size(e))
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

        min_expr_len = 120
        planning = False
        candidates = sorted((k for k, n in counts.items() if n >= 2),
                            key=lambda k: (ast_sizes[k], k))
        for k in candidates:
            e, ev = reps[k]
            body_after_sub = expand(e, ev)
            if len(body_after_sub) >= min_expr_len or (counts[k] >= 4 and len(body_after_sub) >= 75):
                shared[k] = f'{pfx}_expr_{len(shared)}'
                shared_bodies[k] = body_after_sub
        return render_expr, shared, shared_bodies

    exp, shared_helpers, shared_bodies = exp_builder()

    # Anti-unification template outliner for large strict expression skeletons (e.g. packet framing)
    def build_templates():
        def raw_concat_leaves_t(node):
            if isinstance(node, dict) and node.get('op') == 'bytes_concat':
                return raw_concat_leaves_t(node['args'][0]) + raw_concat_leaves_t(node['args'][1])
            return [node]

        def is_leaf_t(node):
            return not (isinstance(node, dict) and 'op' in node)

        def match_u16_t(node):
            if not (isinstance(node, dict) and node.get('op') == 'add'):
                return None
            lhs, rhs = node['args']
            if not (isinstance(lhs, dict) and lhs.get('op') == 'mul' and type(lhs['args'][1]) is int and lhs['args'][1] == 256):
                return None
            at0 = lhs['args'][0]
            if not (isinstance(at0, dict) and at0.get('op') == 'bytes_at_or_zero'):
                return None
            if not (isinstance(rhs, dict) and rhs.get('op') == 'bytes_at_or_zero'):
                return None
            b0, o0 = at0['args']
            b1, o1 = rhs['args']
            if b0 != b1 or not (is_leaf_t(b0) or is_leaf_t(o0)):
                return None
            if type(o0) is int and type(o1) is int and o1 == o0 + 1:
                return (b0, o0)
            if isinstance(o0, dict) and o1 == {'op': 'add', 'args': [o0, 1]}:
                return (b0, o0)
            return None

        def match_u32_t(node):
            if not (isinstance(node, dict) and node.get('op') == 'add'):
                return None
            lhs, rhs = node['args']
            if not (isinstance(lhs, dict) and lhs.get('op') == 'mul' and type(lhs['args'][1]) is int and lhs['args'][1] == 65536):
                return None
            hi = match_u16_t(lhs['args'][0])
            lo = match_u16_t(rhs)
            if not hi or not lo or hi[0] != lo[0]:
                return None
            b0, o0 = hi
            _, o2 = lo
            if type(o0) is int and type(o2) is int and o2 == o0 + 2:
                return (b0, o0)
            if isinstance(o0, dict) and o2 == {'op': 'add', 'args': [o0, 2]}:
                return (b0, o0)
            return None

        def render_concat_strs(strs):
            if len(strs) == 1:
                return strs[0]
            if len(strs) == 2:
                return f'fsa_concat(arena, {strs[0]}, {strs[1]}, {PFX}_BYTE_CAP, err)'
            if len(strs) == 3:
                return f'fsa_concat3(arena, {strs[0]}, {strs[1]}, {strs[2]}, {PFX}_BYTE_CAP, err)'
            if len(strs) == 4:
                return f'fsa_concat4(arena, {strs[0]}, {strs[1]}, {strs[2]}, {strs[3]}, {PFX}_BYTE_CAP, err)'
            acc = render_concat_strs(strs[:4])
            idx = 4
            while idx < len(strs):
                rem = len(strs) - idx
                if rem == 1:
                    acc = f'fsa_concat(arena, {acc}, {strs[idx]}, {PFX}_BYTE_CAP, err)'
                    idx += 1
                elif rem == 2:
                    acc = f'fsa_concat3(arena, {acc}, {strs[idx]}, {strs[idx + 1]}, {PFX}_BYTE_CAP, err)'
                    idx += 2
                else:
                    acc = f'fsa_concat4(arena, {acc}, {strs[idx]}, {strs[idx + 1]}, {strs[idx + 2]}, {PFX}_BYTE_CAP, err)'
                    idx += 3
            return acc

        def apply_strict_op(op_tag, args_c):
            if op_tag == 'concat_n':
                return render_concat_strs(args_c)
            if op_tag == 'u32be':
                return f'fsa_read_u32be({args_c[0]}, {args_c[1]}, {PFX}_BYTE_CAP, err)'
            if op_tag == 'u16be':
                return f'fsa_read_u16be({args_c[0]}, {args_c[1]}, {PFX}_BYTE_CAP, err)'
            if op_tag == 'bytes_eq':
                return f'fsa_slice_eq({args_c[0]}, {args_c[1]})'
            if op_tag == 'bytes_ne':
                return f'(!fsa_slice_eq({args_c[0]}, {args_c[1]}))'
            if op_tag == 'bytes_len':
                return f'((int64_t)({args_c[0]}).len)'
            if op_tag == 'bytes_slice':
                return f'fsa_slice_sub({args_c[0]}, {args_c[1]}, {args_c[2]}, {PFX}_BYTE_CAP, err)'
            if op_tag == 'bytes_at_or_zero':
                return f'fsa_slice_at_or_zero({args_c[0]}, {args_c[1]}, {PFX}_BYTE_CAP, err)'
            if op_tag == 'bytes_pack8_mod':
                return f'fsa_pack8(arena, {args_c[0]}, {PFX}_BYTE_CAP, err)'
            if op_tag == 'bytes_pack16be_mod':
                return f'fsa_pack16be(arena, {args_c[0]}, {PFX}_BYTE_CAP, err)'
            if op_tag == 'bytes_pack32be_mod':
                return f'fsa_pack32be(arena, {args_c[0]}, {PFX}_BYTE_CAP, err)'
            if op_tag == 'bytes_internet_checksum16':
                return f'fsa_checksum16({args_c[0]}, {PFX}_BYTE_CAP, err)'
            binary = {'eq': '==', 'ne': '!=', 'le': '<=', 'ge': '>=', 'and': '&&', 'or': '||'}
            if op_tag in binary:
                return f'({args_c[0]} {binary[op_tag]} {args_c[1]})'
            if op_tag == 'implies':
                return f'(!{args_c[0]} || {args_c[1]})'
            if op_tag == 'ite':
                return f'({args_c[0]} ? {args_c[1]} : {args_c[2]})'
            if op_tag == 'not':
                return f'(!{args_c[0]})'
            if op_tag == 'seq_lt':
                return f'fsa_seq_lt({args_c[0]}, {args_c[1]})'
            if op_tag == 'seq_le':
                return f'fsa_seq_le({args_c[0]}, {args_c[1]})'
            if op_tag == 'seq_comparable':
                return f'fsa_seq_comparable({args_c[0]}, {args_c[1]})'
            if op_tag == 'seq_add':
                return f'fsa_seq_add({args_c[0]}, {args_c[1]})'
            if op_tag == 'seq_distance':
                return f'fsa_seq_dist({args_c[0]}, {args_c[1]})'
            if op_tag == 'min':
                return f'fsa_min({args_c[0]}, {args_c[1]})'
            return {'add': 'fsa_add', 'sub': 'fsa_sub', 'mul': 'fsa_mul'}[op_tag] + f'({args_c[0]}, {args_c[1]}, err)'

        def plain_leaf_c(e, event):
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
                return 'fsa_slice_make(NULL, 0U)' if sym is None else f'fsa_slice_make({sym}, {len(e["bytes"])}U)'
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
                return f'ev[{fi}].bytes' if spec['fields'][name] == 'bytes' else f'ev[{fi}].i64'
            if 'state' in e:
                return f'(m->state == {states.index(e["state"])})'
            if 'timer_active' in e:
                return f'(m->active[{timers.index(e["timer_active"])}] != 0)'
            raise AssertionError(f'Unexpected leaf: {e}')

        # CTree tuple: (ctype, op_tag, children_tuple, exact_c, node_count, ast_node, event)
        def build_ctree(e, event):
            if not (isinstance(e, dict) and 'op' in e):
                ctype = 'fsa_slice_t' if infer(e, model, event) == 'bytes' else 'int64_t'
                return (ctype, 'leaf', (), plain_leaf_c(e, event), 1, e, event)
            op = e['op']
            if op == 'bytes_concat':
                leaves = raw_concat_leaves_t(e)
                non_empty = [
                    lf for lf in leaves
                    if not (isinstance(lf, dict) and 'bytes' in lf and len(lf['bytes']) == 0)
                ]
                if len(non_empty) == 0:
                    return ('fsa_slice_t', 'leaf', (), 'fsa_slice_make(NULL, 0U)', 1, e, event)
                if len(non_empty) == 1 and isinstance(non_empty[0], dict) and ('var' in non_empty[0] or 'bytes' in non_empty[0]):
                    return build_ctree(non_empty[0], event)
                use_leaves = non_empty if len(non_empty) >= 2 else leaves
                ch = tuple(build_ctree(lf, event) for lf in use_leaves)
                ec = apply_strict_op('concat_n', [x[3] for x in ch])
                return ('fsa_slice_t', 'concat_n', ch, ec, 1 + sum(x[4] for x in ch), e, event)
            if op == 'add':
                m32 = match_u32_t(e)
                if m32 is not None:
                    ch = (build_ctree(m32[0], event), build_ctree(m32[1], event))
                    return ('int64_t', 'u32be', ch, apply_strict_op('u32be', [ch[0][3], ch[1][3]]), 1 + ch[0][4] + ch[1][4], e, event)
                m16 = match_u16_t(e)
                if m16 is not None:
                    ch = (build_ctree(m16[0], event), build_ctree(m16[1], event))
                    return ('int64_t', 'u16be', ch, apply_strict_op('u16be', [ch[0][3], ch[1][3]]), 1 + ch[0][4] + ch[1][4], e, event)
            ch = tuple(build_ctree(a, event) for a in e['args'])
            op_tag = op
            if op in ('eq', 'ne') and ch[0][0] == 'fsa_slice_t':
                op_tag = 'bytes_eq' if op == 'eq' else 'bytes_ne'
            ctype = 'fsa_slice_t' if infer(e, model, event) == 'bytes' else 'int64_t'
            ec = apply_strict_op(op_tag, [x[3] for x in ch])
            return (ctype, op_tag, ch, ec, 1 + sum(x[4] for x in ch), e, event)

        def make_tail_node(children_slice, ev):
            if len(children_slice) == 1:
                return children_slice[0]
            ec = apply_strict_op('concat_n', [x[3] for x in children_slice])
            return ('fsa_slice_t', 'concat_n', children_slice, ec, 1 + sum(x[4] for x in children_slice), None, ev)

        def ctree_to_ttree(ct):
            # TTree: (ctype, op_tag, children_tuple, c_str, depth)
            if ct[1] == 'leaf' or not ct[2]:
                return (ct[0], 'leaf', (), ct[3], 1)
            ch = tuple(ctree_to_ttree(x) for x in ct[2])
            return (ct[0], ct[1], ch, ct[3], 1 + max(x[4] for x in ch))

        def cse_ttree_roots(roots):
            total_cnt = Counter()
            strict_set = set()
            info = {}

            def visit(tt, is_strict):
                c_s = tt[3]
                if tt[1] != 'leaf' and tt[2]:
                    total_cnt[c_s] += 1
                    if is_strict:
                        strict_set.add(c_s)
                    if c_s not in info:
                        info[c_s] = tt
                    op_t = tt[1]
                    for ci, child in enumerate(tt[2]):
                        ch_strict = is_strict and (op_t not in ('and', 'or', 'implies', 'ite') or ci == 0)
                        visit(child, ch_strict)

            for rt in roots:
                visit(rt, True)

            chosen = sorted(
                (cs for cs in strict_set if total_cnt[cs] >= 2 and len(cs) >= 55),
                key=lambda cs: (info[cs][4], len(cs), cs),
            )
            if not chosen:
                return [], [rt[3] for rt in roots]

            sub_map = {}

            def render_sub(tt):
                if tt[3] in sub_map:
                    return sub_map[tt[3]]
                if tt[1] == 'leaf' or not tt[2]:
                    return tt[3]
                return apply_strict_op(tt[1], [render_sub(x) for x in tt[2]])

            cse_decls = []
            for cs in chosen:
                tt = info[cs]
                body_sub = apply_strict_op(tt[1], [render_sub(x) for x in tt[2]])
                if len(body_sub) < 48:
                    continue
                vname = f'_tcse_{len(cse_decls)}'
                cse_decls.append(f'    {tt[0]} {vname} = {body_sub};')
                sub_map[cs] = vname
            return cse_decls, [render_sub(rt) for rt in roots]

        def lgg_group(trees):
            param_map = {}
            param_specs = []
            param_keys = []

            def rollback_to(n_saved):
                while len(param_specs) > n_saved:
                    param_specs.pop()
                    k_rem = param_keys.pop()
                    del param_map[k_rem]

            def walk(grp):
                # Returns (TTree, fixed_nodes)
                c0 = grp[0][0]
                op0 = grp[0][1]
                if not op0.startswith('emit:') and len({g[3] for g in grp}) == 1:
                    return ctree_to_ttree(grp[0]), grp[0][4]
                if op0.startswith('emit:') and all(g[1] == op0 for g in grp):
                    m = len(grp[0][2])
                    res = [walk([g[2][i] for g in grp]) for i in range(m)]
                    ch_t = tuple(r[0] for r in res)
                    return ('void', op0, ch_t, '||EMIT_SEP||'.join(x[3] for x in ch_t), 1 + max((x[4] for x in ch_t), default=0)), 2 + sum(r[1] for r in res)
                if op0 in ('and', 'or', 'implies') and all(g[1] == op0 for g in grp):
                    snap = len(param_specs)
                    r0 = walk([g[2][0] for g in grp])
                    after_lhs = len(param_specs)
                    r1 = walk([g[2][1] for g in grp])
                    if len(param_specs) == after_lhs:
                        ch_t = (r0[0], r1[0])
                        ec = apply_strict_op(op0, [r0[0][3], r1[0][3]])
                        return (c0, op0, ch_t, ec, 1 + max(r0[0][4], r1[0][4])), 1 + r0[1] + r1[1]
                    rollback_to(snap)
                elif op0 == 'ite' and all(g[1] == 'ite' for g in grp):
                    snap = len(param_specs)
                    r0 = walk([g[2][0] for g in grp])
                    after_cond = len(param_specs)
                    r1 = walk([g[2][1] for g in grp])
                    r2 = walk([g[2][2] for g in grp])
                    if len(param_specs) == after_cond:
                        ch_t = (r0[0], r1[0], r2[0])
                        ec = apply_strict_op('ite', [r0[0][3], r1[0][3], r2[0][3]])
                        return (c0, 'ite', ch_t, ec, 1 + max(r0[0][4], r1[0][4], r2[0][4])), 1 + r0[1] + r1[1] + r2[1]
                    rollback_to(snap)
                elif op0 == 'concat_n' and all(g[1] == 'concat_n' for g in grp):
                    lens = {len(g[2]) for g in grp}
                    if len(lens) == 1:
                        m = next(iter(lens))
                        res = [walk([g[2][i] for g in grp]) for i in range(m)]
                        ch_t = tuple(r[0] for r in res)
                        ec = apply_strict_op('concat_n', [x[3] for x in ch_t])
                        return (c0, 'concat_n', ch_t, ec, 1 + max(x[4] for x in ch_t)), 1 + sum(r[1] for r in res)
                    m_min = min(lens)
                    if m_min >= 5:
                        res = [walk([g[2][i] for g in grp]) for i in range(m_min - 1)]
                        tails = [make_tail_node(g[2][m_min - 1:], g[6]) for g in grp]
                        tres = walk(tails)
                        res.append(tres)
                        ch_t = tuple(r[0] for r in res)
                        ec = apply_strict_op('concat_n', [x[3] for x in ch_t])
                        return (c0, 'concat_n', ch_t, ec, 1 + max(x[4] for x in ch_t)), 1 + sum(r[1] for r in res)
                elif op0 not in ('leaf', 'and', 'or', 'implies', 'ite') and all(g[1] == op0 and len(g[2]) == len(grp[0][2]) for g in grp):
                    m = len(grp[0][2])
                    res = [walk([g[2][i] for g in grp]) for i in range(m)]
                    ch_t = tuple(r[0] for r in res)
                    ec = apply_strict_op(op0, [x[3] for x in ch_t])
                    return (c0, op0, ch_t, ec, 1 + max(x[4] for x in ch_t)), 1 + sum(r[1] for r in res)
                sig = (c0, tuple(g[3] for g in grp))
                if sig not in param_map:
                    pid = len(param_specs)
                    param_map[sig] = pid
                    param_specs.append((c0, list(grp)))
                    param_keys.append(sig)
                else:
                    pid = param_map[sig]
                return (c0, 'leaf', (), f'_p{pid}', 1), 0

            body_tt, fixed_nodes = walk(trees)
            return body_tt, fixed_nodes, param_specs

        # 1. Cluster whole emit actions first
        emit_occ = []
        for r in model['transitions']:
            ev = r['event']
            for act in r['actions']:
                k, p = next(iter(act.items()))
                if k in ('emit', 'emit_if'):
                    msg_name = p['message']
                    mfields = model['messages'][msg_name]['fields']
                    if not mfields or 'string' in mfields.values():
                        continue
                    mid = messages.index(msg_name)
                    ch = tuple(build_ctree(p['fields'][fn], ev) for fn in mfields)
                    tot_n = 2 + sum(x[4] for x in ch)
                    if tot_n >= 8:
                        ec = f'EMIT_{mid}(' + ', '.join(x[3] for x in ch) + ')'
                        emit_occ.append(((id(act), ev), ('void', f'emit:{mid}', ch, ec, tot_n, p, ev)))

        emit_occ.sort(key=lambda item: (-item[1][4], item[1][3]))
        used_eidx = set()
        covered_val_keys = set()
        etmpl_defs = []
        etmpl_calls = {}
        for i, (okey_i, tr_i) in enumerate(emit_occ):
            if i in used_eidx:
                continue
            compat = []
            for j in range(i + 1, len(emit_occ)):
                if j in used_eidx or emit_occ[j][1][1] != tr_i[1]:
                    continue
                _, fnodes, pspecs = lgg_group([tr_i, emit_occ[j][1]])
                if fnodes >= 6 and len(pspecs) <= 14:
                    compat.append((fnodes, -len(pspecs), j))
            if not compat:
                continue
            compat.sort(reverse=True)
            cluster_indices = [i]
            cur_tt, cur_pspecs = None, None
            for _, _, j in compat:
                cand_trees = [emit_occ[idx][1] for idx in cluster_indices + [j]]
                b_tt, fnodes, pspecs = lgg_group(cand_trees)
                if fnodes >= 6 and len(pspecs) <= 14:
                    cluster_indices.append(j)
                    cur_tt, cur_pspecs = b_tt, pspecs
            if len(cluster_indices) < 2 or cur_tt is None:
                continue
            if (len(cluster_indices) - 1) * len(cur_tt[3]) < 180:
                continue
            etname = f'{pfx}_etmpl_{len(etmpl_defs)}'
            mid = int(tr_i[1].split(':', 1)[1])
            param_types = [ps[0] for ps in cur_pspecs]
            cse_decls, f_strs = cse_ttree_roots(list(cur_tt[2]))
            etmpl_defs.append((etname, mid, param_types, cse_decls, f_strs))
            for pos_k, idx in enumerate(cluster_indices):
                used_eidx.add(idx)
                ok_k = emit_occ[idx][0]
                p_dict = emit_occ[idx][1][5]
                ev_k = emit_occ[idx][1][6]
                for val_e in p_dict['fields'].values():
                    covered_val_keys.add((id(val_e), ev_k))
                arg_nodes = [ps[1][pos_k] for ps in cur_pspecs]
                etmpl_calls[ok_k] = (etname, param_types, arg_nodes)

        # 2. Cluster remaining standalone set/emit value expressions
        occ = []
        for r in model['transitions']:
            ev = r['event']
            for act in r['actions']:
                k, p = next(iter(act.items()))
                if k == 'set':
                    tr = build_ctree(p['value'], ev)
                    if tr[4] >= 14:
                        occ.append(((id(p['value']), ev), tr))
                elif k in ('emit', 'emit_if'):
                    for val_e in p['fields'].values():
                        if (id(val_e), ev) in covered_val_keys:
                            continue
                        tr = build_ctree(val_e, ev)
                        if tr[4] >= 14:
                            occ.append(((id(val_e), ev), tr))

        seen_occ = set()
        uniq_occ = []
        for okey, tr in occ:
            if okey not in seen_occ:
                seen_occ.add(okey)
                uniq_occ.append((okey, tr))
        uniq_occ.sort(key=lambda item: (-item[1][4], item[1][3]))

        used_idx = set()
        tmpl_defs = []
        tmpl_calls = {}
        for i, (okey_i, tr_i) in enumerate(uniq_occ):
            if i in used_idx:
                continue
            compat = []
            for j in range(i + 1, len(uniq_occ)):
                if j in used_idx or uniq_occ[j][1][0] != tr_i[0]:
                    continue
                _, fnodes, pspecs = lgg_group([tr_i, uniq_occ[j][1]])
                if fnodes >= 10 and len(pspecs) <= 14:
                    compat.append((fnodes, -len(pspecs), j))
            if not compat:
                continue
            compat.sort(reverse=True)
            cluster_indices = [i]
            cur_tt, cur_pspecs = None, None
            for _, _, j in compat:
                cand_trees = [uniq_occ[idx][1] for idx in cluster_indices + [j]]
                b_tt, fnodes, pspecs = lgg_group(cand_trees)
                if fnodes >= 10 and len(pspecs) <= 14:
                    cluster_indices.append(j)
                    cur_tt, cur_pspecs = b_tt, pspecs
            if len(cluster_indices) < 2 or cur_tt is None:
                continue
            if (len(cluster_indices) - 1) * len(cur_tt[3]) < 280:
                continue
            tname = f'{pfx}_tmpl_{len(tmpl_defs)}'
            param_types = [ps[0] for ps in cur_pspecs]
            cse_decls, b_strs = cse_ttree_roots([cur_tt])
            tmpl_defs.append((tname, tr_i[0], param_types, cse_decls, b_strs[0]))
            for pos_k, idx in enumerate(cluster_indices):
                used_idx.add(idx)
                ok_k = uniq_occ[idx][0]
                arg_nodes = [ps[1][pos_k] for ps in cur_pspecs]
                tmpl_calls[ok_k] = (tname, param_types, arg_nodes)
        return tmpl_defs, tmpl_calls, etmpl_defs, etmpl_calls

    tmpl_defs, tmpl_calls, etmpl_defs, etmpl_calls = build_templates()

    def render_tmpl_arg(arg_ct):
        if arg_ct[5] is not None:
            return exp(arg_ct[5], arg_ct[6])
        return arg_ct[3]

    # Build header
    h = [
        f'/* Generated by Formal-Spec-Agent ({BACKEND_NAME}) — do not edit manually. */',
        f'#ifndef {PFX}_H',
        f'#define {PFX}_H',
        '',
    ]
    if shared_runtime:
        h.extend([
            '#ifndef FSA_RUNTIME_SHARED',
            '#define FSA_RUNTIME_SHARED 1',
            '#endif',
            '#ifndef FSA_SYSTEM_MODULE',
            '#define FSA_SYSTEM_MODULE 1',
            '#endif',
        ])
    h.extend([
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
    ])

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
        f'int {pfx}_tick_one_ws({pfx}_machine_t *m, int64_t up_to_ms, {pfx}_emit_fn on_emit, void *ctx, '
        f'fsa_arena_t *arena, {pfx}_machine_t *saved_buf, int *last_rule_out);',
        '#ifndef FSA_SYSTEM_MODULE',
        f'int {pfx}_step_with_arena({pfx}_machine_t *m, int64_t now_ms, int event, '
        f'const fsa_val_t *args, int nargs, {pfx}_emit_fn on_emit, void *ctx, '
        f'fsa_arena_t *arena, int *last_rule_out);',
        f'int {pfx}_step({pfx}_machine_t *m, int64_t now_ms, int event, '
        f'const fsa_val_t *args, int nargs, {pfx}_emit_fn on_emit, void *ctx, '
        f'int *last_rule_out);',
        f'int {pfx}_tick({pfx}_machine_t *m, int64_t now_ms, {pfx}_emit_fn on_emit, void *ctx);',
        f'int {pfx}_tick_one({pfx}_machine_t *m, int64_t up_to_ms, {pfx}_emit_fn on_emit, void *ctx, int *last_rule_out);',
        f'const char *{pfx}_string_literal(int64_t str_id);',
        '#endif',
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
        c.append('#ifndef FSA_SYSTEM_MODULE')
        c.append(f'const char *{pfx}_string_literal(int64_t str_id) {{')
        c.append(f'    (void){pfx}_str_len;')
        c.append(f'    if (str_id < 0 || str_id >= {PFX}_NUM_STRINGS) return "";')
        c.append(f'    return {pfx}_str_table[str_id];')
        c.append('}')
        c.append('#endif')
    else:
        c.append('#ifndef FSA_SYSTEM_MODULE')
        c.append(f'static const char *const {pfx}_str_table[1] = {{ "" }};')
        c.append(f'static const uint16_t {pfx}_str_len[1] = {{ 0U }};')
        c.append(f'const char *{pfx}_string_literal(int64_t str_id) {{')
        c.append(f'    (void)str_id; (void){pfx}_str_table; (void){pfx}_str_len;')
        c.append('    return "";')
        c.append('}')
        c.append('#endif')
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

    # Placeholder for live shared pure helpers and parameterized templates
    shared_insert_idx = len(c)

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
    if strings:
        c.append(f'    (void){pfx}_str_table; (void){pfx}_str_len;')
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

    # Emit helpers & Guard / Action functions (deduplicated)
    push_msg_helpers = {}
    if max_emits > 0:
        used_msg_names = {
            next(iter(a.values()))['message']
            for r in model['transitions']
            for a in r['actions']
            if next(iter(a)) in ('emit', 'emit_if')
        }
        c.append('typedef struct {')
        c.append('    int msg_id;')
        c.append('    int nfields;')
        c.append(f'    fsa_val_t fields[{max(max_msg_fields, 1)}];')
        c.append(f'}} {pfx}_pending_emit_t;')
        if any(fkind == 'bytes' for mname in used_msg_names for fkind in model['messages'][mname]['fields'].values()):
            c.extend([
                f'static void {pfx}_pe_bytes({pfx}_pending_emit_t *pe, int j, fsa_slice_t bs, int has_cb, fsa_arena_t *arena, int *err) {{',
                f'    if ((size_t)bs.len > (size_t){PFX}_BYTE_CAP) {{ if (!*err) *err = FSA_ERR_BYTE_CAP; }}',
                f'    else if (has_cb) {{ pe->fields[j] = fsa_val_bytes(NULL, 0); pe->fields[j].bytes = fsa_arena_copy(arena, bs, {PFX}_BYTE_CAP, err); }}',
                '}',
            ])
        c.extend([
            f'static void {pfx}_flush_emits(const {pfx}_pending_emit_t *emits, int nemits, {pfx}_emit_fn on_emit, void *ctx) {{',
            '    if (!on_emit) return;',
            '    for (int k = 0; k < nemits; k++) {',
            '        on_emit(ctx, emits[k].msg_id, emits[k].fields, emits[k].nfields);',
            '    }',
            '}',
        ])
        for mid, msg_name in enumerate(messages):
            if msg_name not in used_msg_names:
                continue
            mfields = model['messages'][msg_name]['fields']
            if 'string' in mfields.values():
                continue
            hname = f'{pfx}_push_msg_{mid}'
            push_msg_helpers[msg_name] = hname
            params = [f'{pfx}_pending_emit_t *pe', 'int has_cb', 'fsa_arena_t *arena', 'int *err']
            for j, (_, fkind) in enumerate(mfields.items()):
                if fkind == 'bytes':
                    params.append(f'fsa_slice_t a{j}')
                elif fkind == 'bool':
                    params.append(f'int a{j}')
                elif fkind == 'seq32':
                    params.append(f'uint32_t a{j}')
                else:
                    params.append(f'int64_t a{j}')
            c.append(f'static void {hname}({", ".join(params)}) {{')
            c.append('    (void)has_cb; (void)arena;')
            c.append('    if (*err) return;')
            c.append(f'    pe->msg_id = {mid};')
            c.append(f'    pe->nfields = {len(mfields)};')
            for j, (_, fkind) in enumerate(mfields.items()):
                if fkind == 'bytes':
                    c.append(f'    {pfx}_pe_bytes(pe, {j}, a{j}, has_cb, arena, err);')
                elif fkind == 'bool':
                    c.append(f'    pe->fields[{j}] = fsa_val_bool(a{j});')
                elif fkind == 'seq32':
                    c.append(f'    pe->fields[{j}] = fsa_val_seq32(a{j});')
                else:
                    c.append(f'    pe->fields[{j}] = fsa_val_int(a{j});')
            c.append('}')
        for etname, mid, ptypes, cse_decls, fbodies in etmpl_defs:
            msg_name = messages[mid]
            mfields = model['messages'][msg_name]['fields']
            hname = push_msg_helpers[msg_name]
            eparams = [
                f'const {pfx}_machine_t *m', 'const fsa_val_t *ev',
                f'{pfx}_pending_emit_t *pe', 'int has_cb', 'fsa_arena_t *arena', 'int *err',
            ] + [f'{pt} _p{pid}' for pid, pt in enumerate(ptypes)]
            c.append(f'static void {etname}({", ".join(eparams)}) {{')
            voids = ['(void)m;', '(void)ev;', '(void)has_cb;', '(void)arena;'] + [f'(void)_p{pid};' for pid in range(len(ptypes))]
            c.append('    ' + ' '.join(voids))
            c.append('    if (*err) return;')
            c.extend(cse_decls)
            call_args = ['pe', 'has_cb', 'arena', 'err']
            for j, ((_, fkind), fb) in enumerate(zip(mfields.items(), fbodies)):
                if fkind == 'bytes':
                    c.append(f'    fsa_slice_t _ef{j} = {fb};')
                elif fkind == 'bool':
                    c.append(f'    int _ef{j} = (int)({fb});')
                elif fkind == 'seq32':
                    c.append(f'    uint32_t _ef{j} = (uint32_t)({fb});')
                else:
                    c.append(f'    int64_t _ef{j} = {fb};')
                call_args.append(f'_ef{j}')
            c.append(f'    {hname}({", ".join(call_args)});')
            c.append('}')
        c.append('')
    if nt > 0 and any(next(iter(a)) in ('arm', 'arm_if') for r in model['transitions'] for a in r['actions']):
        c.extend([
            f'static void {pfx}_arm_tmr({pfx}_machine_t *m, int ti, int64_t delay, int *err) {{',
            '    if (delay <= 0) { if (!*err) *err = FSA_ERR_TIMER_DELAY; return; }',
            '    m->due[ti] = fsa_add(m->now_ms, delay, err);',
            '    if (!*err) m->active[ti] = 1U;',
            '}',
            '',
        ])

    guard_cache = {}
    guard_bodies = []
    rule_guard_idx = []
    for r in model['transitions']:
        ev = r['event']
        g_body = exp(r['guard'], ev)
        if g_body not in guard_cache:
            guard_cache[g_body] = len(guard_bodies)
            guard_bodies.append(g_body)
        rule_guard_idx.append(guard_cache[g_body])
    if guard_bodies:
        c.append(
            f'static int {pfx}_eval_guard(const {pfx}_machine_t *m, const fsa_val_t *ev, '
            f'int gidx, fsa_arena_t *arena, int *err) {{'
        )
        c.append('    (void)m; (void)ev; (void)arena; (void)err;')
        c.append('    switch (gidx) {')
        for gidx, gb in enumerate(guard_bodies):
            c.append(f'        case {gidx}: return ({gb}) != 0;')
        c.append('        default: return 0;')
        c.append('    }')
        c.append('}')
        c.append('')

    def render_val_with_tmpl(val_ast, ev_name, pre_lines, ind, tag):
        okey = (id(val_ast), ev_name)
        if okey not in tmpl_calls:
            return exp(val_ast, ev_name)
        tname, ptypes, arg_cts = tmpl_calls[okey]
        targs = ['m', 'ev', 'arena', 'err']
        for pid, (ptype, act_ct) in enumerate(zip(ptypes, arg_cts)):
            ac = render_tmpl_arg(act_ct)
            vname = f'_tp{tag}_{pid}'
            pre_lines.append(f'{ind}{ptype} {vname} = {ac};')
            targs.append(vname)
        return f'{tname}({", ".join(targs)})'

    # Deduplicate rule action specs (parameterized by target state), then outline repeated action blocks
    unique_specs = []
    spec_index = {}
    rule_spec_idx = []
    rule_to_state = []
    for r in model['transitions']:
        ev = r['event']
        rule_emits = sum(1 for a in r['actions'] if next(iter(a)) in ('emit', 'emit_if'))
        units = []
        for act in r['actions']:
            k, p = next(iter(act.items()))
            ulines = []
            outlinable = True
            if k == 'set':
                name = p['var']
                pre_t = []
                val_c = render_val_with_tmpl(p['value'], ev, pre_t, '        ', 's')
                if pre_t:
                    ulines.append('    {')
                    ulines.extend(pre_t)
                    if name in byte_vars:
                        bi = byte_vars.index(name)
                        ulines.append(f'        fsa_buf_assign(m->bdata[{bi}], &m->blen[{bi}], {PFX}_BYTE_CAP, {val_c}, err);')
                    else:
                        si = scalar_vars.index(name)
                        ulines.append(f'        m->v[{si}] = {val_c};')
                    ulines.append('    }')
                else:
                    if name in byte_vars:
                        bi = byte_vars.index(name)
                        ulines.append(f'    fsa_buf_assign(m->bdata[{bi}], &m->blen[{bi}], {PFX}_BYTE_CAP, {val_c}, err);')
                    else:
                        si = scalar_vars.index(name)
                        ulines.append(f'    m->v[{si}] = {val_c};')
            elif k in ('emit', 'emit_if'):
                indent = '    '
                if k == 'emit_if':
                    ulines.append(f'    if ({exp(p["when"], ev)}) {{')
                    indent = '        '
                msg_name = p['message']
                mid = messages.index(msg_name)
                mfields = model['messages'][msg_name]['fields']
                ulines.append(f'{indent}if (!*err) {{')
                if (id(act), ev) in etmpl_calls:
                    etname, ptypes, arg_cts = etmpl_calls[(id(act), ev)]
                    et_args = ['m', 'ev', '&emits_p[(*nemits_p)++]', 'has_cb', 'arena', 'err']
                    for pid, (ptype, act_ct) in enumerate(zip(ptypes, arg_cts)):
                        ac = render_tmpl_arg(act_ct)
                        vname = f'_tep_{pid}'
                        ulines.append(f'{indent}    {ptype} {vname} = {ac};')
                        et_args.append(vname)
                    ulines.append(f'{indent}    {etname}({", ".join(et_args)});')
                elif msg_name in push_msg_helpers:
                    call_args = ['&emits_p[(*nemits_p)++]', 'has_cb', 'arena', 'err']
                    for j, (fname, fkind) in enumerate(mfields.items()):
                        pre_t = []
                        val_c = render_val_with_tmpl(p['fields'][fname], ev, pre_t, indent + '    ', f'f{j}')
                        ulines.extend(pre_t)
                        if fkind == 'bytes':
                            ulines.append(f'{indent}    fsa_slice_t _ef{j} = {val_c};')
                        elif fkind == 'bool':
                            ulines.append(f'{indent}    int _ef{j} = (int)({val_c});')
                        elif fkind == 'seq32':
                            ulines.append(f'{indent}    uint32_t _ef{j} = (uint32_t)({val_c});')
                        else:
                            ulines.append(f'{indent}    int64_t _ef{j} = {val_c};')
                        call_args.append(f'_ef{j}')
                    ulines.append(f'{indent}    {push_msg_helpers[msg_name]}({", ".join(call_args)});')
                else:
                    ulines.append(f'{indent}    {pfx}_pending_emit_t *pe = &emits_p[(*nemits_p)++];')
                    ulines.append(f'{indent}    pe->msg_id = {mid};')
                    ulines.append(f'{indent}    pe->nfields = {len(mfields)};')
                    for j, (fname, fkind) in enumerate(mfields.items()):
                        pre_t = []
                        val_c = render_val_with_tmpl(p['fields'][fname], ev, pre_t, indent + '    ', f'f{j}')
                        ulines.extend(pre_t)
                        if fkind == 'bytes':
                            ulines.append(f'{indent}    {pfx}_pe_bytes(pe, {j}, {val_c}, has_cb, arena, err);')
                        elif fkind == 'bool':
                            ulines.append(f'{indent}    pe->fields[{j}] = fsa_val_bool((int)({val_c}));')
                        elif fkind == 'seq32':
                            ulines.append(f'{indent}    pe->fields[{j}] = fsa_val_seq32((uint32_t)({val_c}));')
                        elif fkind == 'string':
                            ulines.append(f'{indent}    {{ int64_t sid = {val_c};')
                            if has_text:
                                ulines.append(
                                    f'{indent}      if (sid < 0 || sid >= m->texts.count) {{ if (!*err) *err = FSA_ERR_STRING_DOMAIN; }}'
                                )
                                ulines.append(
                                    f'{indent}      else if (has_cb) {{ pe->fields[{j}] = fsa_val_str(m->texts.data[sid], m->texts.len[sid]); pe->fields[{j}].i64 = sid; }}'
                                )
                            else:
                                ulines.append(
                                    f'{indent}      if (sid < 0 || sid >= {PFX}_NUM_STRINGS) {{ if (!*err) *err = FSA_ERR_STRING_DOMAIN; }}'
                                )
                                ulines.append(
                                    f'{indent}      else if (has_cb) {{ pe->fields[{j}] = fsa_val_str({pfx}_str_table[sid], {pfx}_str_len[sid]); pe->fields[{j}].i64 = sid; }}'
                                )
                            ulines.append(f'{indent}    }}')
                        else:
                            ulines.append(f'{indent}    pe->fields[{j}] = fsa_val_int({val_c});')
                ulines.append(f'{indent}}}')
                if k == 'emit_if':
                    ulines.append('    }')
            elif k in ('arm', 'arm_if'):
                ti = timers.index(p['timer'])
                if k == 'arm_if':
                    ulines.append(f'    if ({exp(p["when"], ev)}) {pfx}_arm_tmr(m, {ti}, {exp(p["delay_ms"], ev)}, err);')
                else:
                    ulines.append(f'    {pfx}_arm_tmr(m, {ti}, {exp(p["delay_ms"], ev)}, err);')
            elif k in ('cancel', 'cancel_if'):
                tname = p if k == 'cancel' else p['timer']
                ti = timers.index(tname)
                if k == 'cancel_if':
                    ulines.append(f'    if ({exp(p["when"], ev)}) m->active[{ti}] = 0U;')
                else:
                    ulines.append(f'    m->active[{ti}] = 0U;')
            if any(re.search(r'\berr\b', ln) for ln in ulines):
                ulines.append('    if (*err) return 0;')
            units.append((outlinable, tuple(ulines)))
        to_st = states.index(r['to'])
        rule_to_state.append(to_st)
        skey = (rule_emits, tuple(units))
        if skey not in spec_index:
            spec_index[skey] = len(unique_specs)
            unique_specs.append([rule_emits, list(units)])
        rule_spec_idx.append(spec_index[skey])

    # Greedy contiguous action-block outlining over all action units (including emits)
    for b_idx in range(32):
        seq_occ = defaultdict(list)
        for uid, (_, units_list) in enumerate(unique_specs):
            n = len(units_list)
            seen_in_u = set()
            i = 0
            while i < n:
                if not units_list[i][0]:
                    i += 1
                    continue
                j = i
                while j < n and units_list[j][0]:
                    j += 1
                if j - i >= 2:
                    for s in range(i, j - 1):
                        for e_idx in range(s + 2, min(j + 1, s + 20)):
                            seq = tuple(units_list[s:e_idx])
                            if seq not in seen_in_u:
                                seen_in_u.add(seq)
                                seq_occ[seq].append((uid, s, e_idx))
                i = j
        best_score = 0
        best_seq = None
        for seq, occs in seq_occ.items():
            freq = 0
            for uid in {o[0] for o in occs}:
                ul = unique_specs[uid][1]
                k = 0
                L = len(seq)
                while k + L <= len(ul):
                    if tuple(ul[k:k + L]) == seq:
                        freq += 1
                        k += L
                    else:
                        k += 1
            if freq >= 2:
                seq_chars = sum(sum(len(ln) for ln in u[1]) for u in seq)
                score = (seq_chars - 70) * (freq - 1) - 120
                if score > best_score:
                    best_score = score
                    best_seq = seq
        if best_score < 120 or best_seq is None:
            break
        bfn = f'{pfx}_act_blk_{b_idx}'
        if max_emits > 0:
            c.append(
                f'static int {bfn}({pfx}_machine_t *m, const fsa_val_t *ev, '
                f'{pfx}_pending_emit_t *emits_p, int *nemits_p, int has_cb, fsa_arena_t *arena, int *err) {{'
            )
            c.append('    (void)m; (void)ev; (void)emits_p; (void)nemits_p; (void)has_cb; (void)arena; (void)err;')
            call_unit = (True, (f'    if (!{bfn}(m, ev, emits_p, nemits_p, has_cb, arena, err)) return 0;',))
        else:
            c.append(f'static int {bfn}({pfx}_machine_t *m, const fsa_val_t *ev, fsa_arena_t *arena, int *err) {{')
            c.append('    (void)m; (void)ev; (void)arena; (void)err;')
            call_unit = (True, (f'    if (!{bfn}(m, ev, arena, err)) return 0;',))
        for _, ulines in best_seq:
            c.extend(ulines)
        c.append('    return *err == FSA_OK;')
        c.append('}')
        c.append('')
        L = len(best_seq)
        for spec in unique_specs:
            old_u = spec[1]
            new_u = []
            k = 0
            while k < len(old_u):
                if k + L <= len(old_u) and tuple(old_u[k:k + L]) == best_seq:
                    new_u.append(call_unit)
                    k += L
                else:
                    new_u.append(old_u[k])
                    k += 1
            spec[1] = new_u

    if unique_specs:
        c.append(
            f'static int {pfx}_run_action({pfx}_machine_t *m, const fsa_val_t *ev, int aidx, int next_st, '
            f'fsa_arena_t *arena, {pfx}_emit_fn on_emit, void *ctx, int *err) {{'
        )
        c.append('    (void)m; (void)ev; (void)arena; (void)on_emit; (void)ctx; (void)err;')
        if max_emits > 0:
            c.append(f'    {pfx}_pending_emit_t emits[{max_emits}];')
            c.append('    int nemits = 0;')
            c.append('    memset(emits, 0, sizeof(emits));')
            c.append(f'    {pfx}_pending_emit_t *emits_p = emits;')
            c.append('    int *nemits_p = &nemits;')
            c.append('    int has_cb = (on_emit != NULL);')
            c.append('    (void)emits_p; (void)nemits_p; (void)has_cb;')
        c.append('    switch (aidx) {')
        for uid, (_, units_list) in enumerate(unique_specs):
            c.append(f'        case {uid}: {{')
            for _, ulines in units_list:
                for uln in ulines:
                    c.append('        ' + uln)
            c.append('            break;')
            c.append('        }')
        c.append('        default: *err = FSA_ERR_INVALID_ARG; return 0;')
        c.append('    }')
        c.append('    if (*err) return 0;')
        c.append('    m->state = next_st;')
        c.append(f'#if {PFX}_CHECK_INVARIANTS')
        c.append(f'    if (!{pfx}_check_inv_err(m, arena, err)) return 0;')
        c.append('#endif')
        if max_emits > 0:
            c.append(f'    {pfx}_flush_emits(emits, nemits, on_emit, ctx);')
        c.append('    return *err == FSA_OK;')
        c.append('}')
        c.append('')

    # Precompute decision trees per (state_idx, event_idx)
    constraints_by_rule = [_extract_eq_constraints(r['guard'], model, strings) for r in model['transitions']]
    buckets_se = defaultdict(list)
    for idx, r in enumerate(model['transitions']):
        buckets_se[(states.index(r['from']), events.index(r['event']))].append(idx)
    trees_se = {
        k: _partition_rules(rlist, constraints_by_rule, set())
        for k, rlist in buckets_se.items()
    }

    leaf_bucket_map = {}
    leaf_bucket_list = []

    def collect_leaf_buckets(node):
        tag = node[0]
        if tag == 'empty':
            return
        if tag == 'leaf':
            if node[1]:
                tkey = tuple(node[1])
                if tkey not in leaf_bucket_map:
                    leaf_bucket_map[tkey] = len(leaf_bucket_list)
                    leaf_bucket_list.append(tkey)
            return
        _, _, cases, default_node = node
        for _, child in cases:
            collect_leaf_buckets(child)
        collect_leaf_buckets(default_node)

    for sidx in range(len(states)):
        for ev_i in sorted(ev_i for (st_i, ev_i) in trees_se if st_i == sidx):
            collect_leaf_buckets(trees_se[(sidx, ev_i)])

    switch_se = {
        (s, e): tree for (s, e), tree in trees_se.items() if tree[0] == 'switch'
    }

    if (events or nt > 0) and model['transitions']:
        c.extend([
            f'static const uint16_t {pfx}_rule_gidx[] = {{ {", ".join(str(x) + "U" for x in rule_guard_idx)} }};',
            f'static const uint16_t {pfx}_rule_aidx[] = {{ {", ".join(str(x) + "U" for x in rule_spec_idx)} }};',
            f'static const uint16_t {pfx}_rule_to_state[] = {{ {", ".join(str(x) + "U" for x in rule_to_state)} }};',
        ])
        flat_bkt_rules = []
        bkt_offs = []
        bkt_lens = []
        for bkt in leaf_bucket_list:
            bkt_offs.append(len(flat_bkt_rules))
            bkt_lens.append(len(bkt))
            flat_bkt_rules.extend(bkt)
        if flat_bkt_rules:
            c.append(f'static const uint16_t {pfx}_bkt_rules[] = {{ {", ".join(str(r) + "U" for r in flat_bkt_rules)} }};')
            c.append(f'static const uint16_t {pfx}_bkt_off[] = {{ {", ".join(str(o) + "U" for o in bkt_offs)} }};')
            c.append(f'static const uint16_t {pfx}_bkt_len[] = {{ {", ".join(str(ln) + "U" for ln in bkt_lens)} }};')
        ev_dim = max(len(events), 1)
        c.append(f'static const int16_t {pfx}_se_bkt[{len(states)}][{ev_dim}] = {{')
        for sidx in range(len(states)):
            row = []
            for ev_i in range(ev_dim):
                tr = trees_se.get((sidx, ev_i))
                if tr is not None and tr[0] == 'leaf' and tr[1]:
                    row.append(str(leaf_bucket_map[tuple(tr[1])]))
                else:
                    row.append('-1')
            c.append('    { ' + ', '.join(row) + ' },')
        c.append('};')
        c.extend([
            f'static void {pfx}_eval_bucket(const {pfx}_machine_t *m, const fsa_val_t *ev, fsa_arena_t *arena, '
            f'uint32_t saved_used, const uint16_t *rlist, int n, int *match, int *count, int *err) {{',
            '    (void)count;',
            '    for (int i = 0; i < n; i++) {',
            '        uint16_t r = rlist[i];',
            '        arena->used = saved_used;',
            f'        if ({pfx}_eval_guard(m, ev, (int){pfx}_rule_gidx[r], arena, err)) {{',
            f'#if {PFX}_CHECK_CONFLICTS',
            '            *match = (int)r;',
            '            (*count)++;',
            '#else',
            '            *match = (int)r;',
            '            return;',
            '#endif',
            '        }',
            '    }',
            '}',
            '',
        ])

    def emit_leaf_eval(lines_out, rules_list, ind):
        if not rules_list:
            return
        bid = leaf_bucket_map[tuple(rules_list)]
        lines_out.append(
            f'{ind}{pfx}_eval_bucket(m, ev, arena, saved_used, '
            f'&{pfx}_bkt_rules[{pfx}_bkt_off[{bid}]], (int){pfx}_bkt_len[{bid}], &match, &count, err);'
        )
        lines_out.append(f'{ind}#if !{PFX}_CHECK_CONFLICTS')
        lines_out.append(f'{ind}if (match >= 0) goto matched;')
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
        # Fast O(1) decision-tree + 2D table fire dispatcher
        c.append(
            f'static int {pfx}_fire({pfx}_machine_t *m, int event, const fsa_val_t *ev, '
            f'int expiring, fsa_arena_t *arena, {pfx}_emit_fn on_emit, void *ctx, int *last_rule_out, int *err) {{'
        )
        if not model['transitions']:
            c.append('    (void)m; (void)event; (void)ev; (void)expiring; (void)arena; (void)on_emit; (void)ctx; (void)last_rule_out;')
            c.append('    *err = FSA_ERR_UNCOVERED;')
            c.append('    return 0;')
            c.append('}')
            c.append('')
        else:
            c.append('    (void)event; (void)ev; (void)on_emit; (void)ctx; (void)last_rule_out;')
            c.append('    int match = -1;')
            c.append('    int count = 0;')
            c.append('    int handled = 0;')
            c.append('    (void)count;')
            c.append('    uint32_t saved_used = arena->used;')
            if switch_se:
                c.append('    switch (m->state) {')
                for sidx in sorted({s for (s, _) in switch_se}):
                    c.append(f'        case {sidx}: {{')
                    c.append('            switch (event) {')
                    for ev_i in sorted(e for (s, e) in switch_se if s == sidx):
                        c.append(f'                case {ev_i}: {{')
                        c.append('                    handled = 1;')
                        emit_tree(c, switch_se[(sidx, ev_i)], '                    ')
                        c.append('                    break;')
                        c.append('                }')
                    c.append('                default: break;')
                    c.append('            }')
                    c.append('            break;')
                    c.append('        }')
                c.append('        default: break;')
                c.append('    }')
            c.append(f'    if (!handled && m->state >= 0 && m->state < {len(states)} && event >= 0 && event < {ev_dim}) {{')
            c.append(f'        int16_t bid = {pfx}_se_bkt[m->state][event];')
            if flat_bkt_rules:
                c.append('        if (bid >= 0) {')
                c.append(
                    f'            {pfx}_eval_bucket(m, ev, arena, saved_used, '
                    f'&{pfx}_bkt_rules[{pfx}_bkt_off[bid]], (int){pfx}_bkt_len[bid], &match, &count, err);'
                )
                c.append('        }')
            else:
                c.append('        (void)bid;')
            c.append('    }')
            if switch_se:
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
            c.append(
                f'    return {pfx}_run_action(m, ev, (int){pfx}_rule_aidx[match], (int){pfx}_rule_to_state[match], '
                f'arena, on_emit, ctx, err);'
            )
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
    c.append('    if (!m || !arena || !arena->buf) return -FSA_ERR_INVALID_ARG;')
    c.append(f'#if {PFX}_ATOMIC_ROLLBACK')
    c.append('    if (!saved_buf) return -FSA_ERR_INVALID_ARG;')
    c.append('#endif')
    c.append('    if (last_rule_out) *last_rule_out = -1;')
    if not events:
        c.append(f'    (void){pfx}_event_origin; (void){pfx}_event_nfields; (void){pfx}_event_kinds; (void)args;')
        c.append('    if (event >= 0 || nargs != 0) return -FSA_ERR_INVALID_ARG;')
        c.append(f'#if {PFX}_ATOMIC_ROLLBACK')
        c.append('    *saved_buf = *m;')
        c.append('#else')
        c.append('    (void)saved_buf;')
        c.append('#endif')
    elif not has_text:
        c.append('    memset(ev_norm, 0, sizeof(ev_norm));')
        c.append(
            f'    err = fsa_norm_event_args(event, {PFX}_NUM_EVENTS, {pfx}_event_origin, '
            f'{pfx}_event_nfields, &{pfx}_event_kinds[0][0], {max(max_ef, 1)}, args, nargs, {PFX}_BYTE_CAP, ev_norm);'
        )
        c.append('    if (err) return -err;')
        c.append(f'#if {PFX}_ATOMIC_ROLLBACK')
        c.append('    *saved_buf = *m;')
        c.append('#else')
        c.append('    (void)saved_buf;')
        c.append('#endif')
    else:
        c.append('    memset(ev_norm, 0, sizeof(ev_norm));')
        c.append('    if (event >= 0) {')
        c.append(f'        if (event >= {PFX}_NUM_EVENTS) return -FSA_ERR_INVALID_ARG;')
        c.append(f'        if ({pfx}_event_origin[event]) return -FSA_ERR_INVALID_ARG;')
        c.append(f'        if (nargs != {pfx}_event_nfields[event] || (nargs > 0 && !args)) return -FSA_ERR_INVALID_ARG;')
        c.append('    } else if (nargs != 0) {')
        c.append('        return -FSA_ERR_INVALID_ARG;')
        c.append('    }')
        c.append(f'#if {PFX}_ATOMIC_ROLLBACK')
        c.append('    *saved_buf = *m;')
        c.append('#else')
        c.append('    (void)saved_buf;')
        c.append('#endif')
        c.append('    if (event >= 0) {')
        c.append('        for (int i = 0; i < nargs; i++) {')
        c.append(f'            uint8_t k = {pfx}_event_kinds[event][i];')
        c.append('            if (args[i].kind != k) { err = FSA_ERR_INVALID_ARG; goto fail; }')
        c.append('            ev_norm[i] = args[i];')
        c.append(f'            if (k == FSA_KIND_BYTES) {{ if (args[i].bytes.len > 0 && !args[i].bytes.ptr) {{ err = FSA_ERR_INVALID_ARG; goto fail; }} if ((size_t)args[i].bytes.len > (size_t){PFX}_BYTE_CAP) {{ err = FSA_ERR_BYTE_CAP; goto fail; }} }}')
        c.append('            else if (k == FSA_KIND_BOOL) { if (args[i].i64 != 0 && args[i].i64 != 1) { err = FSA_ERR_INVALID_ARG; goto fail; } }')
        c.append('            else if (k == FSA_KIND_SEQ32) { if (args[i].i64 < 0 || args[i].i64 >= FSA_SEQ_MOD) { err = FSA_ERR_INVALID_ARG; goto fail; } }')
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
        '#ifndef FSA_SYSTEM_MODULE',
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
        '#endif',
        '',
    ])

    # Emit only transitively referenced shared_helpers plus parameterized templates
    tail_text = '\n'.join(c[shared_insert_idx:])
    tmpl_text = (
        '\n'.join('\n'.join(cd) + '\n' + tb for _, _, _, cd, tb in tmpl_defs)
        + '\n'
        + '\n'.join('\n'.join(cd) + '\n' + '\n'.join(fbs) for _, _, _, cd, fbs in etmpl_defs)
    )
    live_fnames = set(re.findall(rf'\b{re.escape(pfx)}_expr_\d+\b', tail_text + '\n' + tmpl_text))
    fname_to_key = {fn: k for k, fn in shared_helpers.items()}
    work = list(live_fnames)
    while work:
        cur_fn = work.pop()
        if cur_fn in fname_to_key:
            btxt = shared_bodies[fname_to_key[cur_fn]]
            for ref_fn in re.findall(rf'\b{re.escape(pfx)}_expr_\d+\b', btxt):
                if ref_fn not in live_fnames:
                    live_fnames.add(ref_fn)
                    work.append(ref_fn)

    helper_lines = []
    live_helper_count = 0
    for (kind, srep), fname in shared_helpers.items():
        if fname not in live_fnames:
            continue
        live_helper_count += 1
        body = shared_bodies[(kind, srep)]
        helper_lines.append(
            f'static {kind} {fname}(const {pfx}_machine_t *m, const fsa_val_t *ev, '
            f'fsa_arena_t *arena, int *err) {{'
        )
        helper_lines.append('    (void)m; (void)ev; (void)arena; (void)err;')
        helper_lines.append(f'    return {body};')
        helper_lines.append('}')
    for tname, rtype, ptypes, cse_decls, tbody in tmpl_defs:
        tparams = [
            f'const {pfx}_machine_t *m', 'const fsa_val_t *ev',
            'fsa_arena_t *arena', 'int *err',
        ] + [f'{pt} _p{pid}' for pid, pt in enumerate(ptypes)]
        helper_lines.append(f'static {rtype} {tname}({", ".join(tparams)}) {{')
        voids = ['(void)m;', '(void)ev;', '(void)arena;', '(void)err;'] + [f'(void)_p{pid};' for pid in range(len(ptypes))]
        helper_lines.append('    ' + ' '.join(voids))
        helper_lines.extend(cse_decls)
        helper_lines.append(f'    return {tbody};')
        helper_lines.append('}')
    if helper_lines:
        helper_lines.append('')
        c[shared_insert_idx:shared_insert_idx] = helper_lines

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
        'shared_helpers': live_helper_count + len(tmpl_defs),
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
