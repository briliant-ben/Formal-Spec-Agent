"""Typed Python AST builder helpers for declarative Protocol IR 0.6 models."""
import json
from pathlib import Path

from protocol_lab.codegen import admit
from protocol_lab.ir import validate


def var(name):
    return {"var": str(name)}


def ev(name):
    return {"event": str(name)}


def state_is(name):
    return {"state": str(name)}


def timer_on(name):
    return {"timer_active": str(name)}


def seq_lit(value):
    return {"seq": int(value) & 0xFFFFFFFF}


def bytes_lit(values):
    return {"bytes": [int(x) & 0xFF for x in values]}


def not_(expr):
    return {"op": "not", "args": [expr]}


def implies_(lhs, rhs):
    return {"op": "implies", "args": [lhs, rhs]}


def eq_(lhs, rhs):
    return {"op": "eq", "args": [lhs, rhs]}


def ne_(lhs, rhs):
    return {"op": "ne", "args": [lhs, rhs]}


def le_(lhs, rhs):
    return {"op": "le", "args": [lhs, rhs]}


def ge_(lhs, rhs):
    return {"op": "ge", "args": [lhs, rhs]}


def lt_(lhs, rhs):
    return not_(ge_(lhs, rhs))


def gt_(lhs, rhs):
    return not_(le_(lhs, rhs))


def ite_(cond, when_true, when_false):
    return {"op": "ite", "args": [cond, when_true, when_false]}


def and_(*args):
    if not args:
        return True
    acc = args[0]
    for nxt in args[1:]:
        acc = {"op": "and", "args": [acc, nxt]}
    return acc


def or_(*args):
    if not args:
        return False
    acc = args[0]
    for nxt in args[1:]:
        acc = {"op": "or", "args": [acc, nxt]}
    return acc


def add_(*args):
    if not args:
        return 0
    acc = args[0]
    for nxt in args[1:]:
        acc = {"op": "add", "args": [acc, nxt]}
    return acc


def sub_(lhs, rhs):
    return {"op": "sub", "args": [lhs, rhs]}


def mul_(*args):
    if not args:
        return 1
    acc = args[0]
    for nxt in args[1:]:
        acc = {"op": "mul", "args": [acc, nxt]}
    return acc


def min_(*args):
    if len(args) < 1:
        raise ValueError("min_ requires at least one argument")
    acc = args[0]
    for nxt in args[1:]:
        acc = {"op": "min", "args": [acc, nxt]}
    return acc


def max_(lhs, rhs):
    return ite_(ge_(lhs, rhs), lhs, rhs)


def clamp_(val, lo, hi):
    return min_(max_(val, lo), hi)


def seq_add_(base, delta):
    return {"op": "seq_add", "args": [base, delta]}


def seq_dist_(a, b):
    return {"op": "seq_distance", "args": [a, b]}


def seq_comp_(a, b):
    return {"op": "seq_comparable", "args": [a, b]}


def seq_lt_(a, b):
    return {"op": "seq_lt", "args": [a, b]}


def seq_le_(a, b):
    return {"op": "seq_le", "args": [a, b]}


def seq_gt_(a, b):
    return and_(seq_comp_(a, b), not_(seq_le_(a, b)))


def seq_ge_(a, b):
    return and_(seq_comp_(a, b), not_(seq_lt_(a, b)))


def b_len(buf):
    return {"op": "bytes_len", "args": [buf]}


def b_slice(buf, offset, count):
    return {"op": "bytes_slice", "args": [buf, offset, count]}


def b_at(buf, offset):
    return {"op": "bytes_at_or_zero", "args": [buf, offset]}


def b_concat(*parts):
    if not parts:
        return bytes_lit([])
    acc = parts[0]
    for nxt in parts[1:]:
        acc = {"op": "bytes_concat", "args": [acc, nxt]}
    return acc


def pack8(val):
    return {"op": "bytes_pack8_mod", "args": [val]}


def pack16be(val):
    return {"op": "bytes_pack16be_mod", "args": [val]}


def pack32be(val):
    return {"op": "bytes_pack32be_mod", "args": [val]}


def pack_seq32be(seq_expr):
    return pack32be(seq_dist_(seq_lit(0), seq_expr))


def csum16(buf):
    return {"op": "bytes_internet_checksum16", "args": [buf]}


def u8(buf, off):
    return b_at(buf, off)


def u16be(buf, off):
    return add_(mul_(b_at(buf, off), 256), b_at(buf, add_(off, 1) if isinstance(off, dict) else off + 1))


def u32be_int(buf, off):
    hi_off = off
    lo_off = add_(off, 2) if isinstance(off, dict) else off + 2
    return add_(mul_(u16be(buf, hi_off), 65536), u16be(buf, lo_off))


def u32be_seq(buf, off):
    return seq_add_(seq_lit(0), u32be_int(buf, off))


def strip_ge(val, bit):
    return ite_(ge_(val, bit), sub_(val, bit), val)


def u8_has_bit(byte_expr, bit):
    """Exact bit test for power-of-two `bit` in {1,2,4,8,16,32,64,128} on an octet 0..255."""
    if bit not in (1, 2, 4, 8, 16, 32, 64, 128):
        raise ValueError(f"bit must be power of two in 1..128, got {bit}")
    rem = byte_expr
    for b in (128, 64, 32, 16, 8, 4, 2, 1):
        if b > bit:
            rem = strip_ge(rem, b)
    return ge_(rem, bit)


def u8_low_nibble(byte_expr):
    rem = byte_expr
    for b in (128, 64, 32, 16):
        rem = strip_ge(rem, b)
    return rem


def u8_hi_nibble(byte_expr):
    """Exact `byte >> 4` for an octet 0..255."""
    return b_at(pack16be(mul_(byte_expr, 16)), 0)


def u8_div2(byte_expr):
    """Exact `byte >> 1` for an octet 0..255."""
    return b_at(pack16be(mul_(byte_expr, 128)), 0)


def u16_div2(u16_expr):
    """Exact `x >> 1` for 0 <= x <= 65535 using big-endian byte split."""
    p = pack16be(u16_expr)
    return add_(mul_(b_at(p, 0), 128), u8_div2(b_at(p, 1)))


def u8_mod8(byte_expr):
    rem = byte_expr
    for b in (128, 64, 32, 16, 8):
        rem = strip_ge(rem, b)
    return rem


def u16_align8_floor(u16_expr):
    """Exact `(x // 8) * 8` for 0 <= x <= 65535."""
    lo = b_at(pack16be(u16_expr), 1)
    return sub_(u16_expr, u8_mod8(lo))


def act_set(var_name, value):
    return {"set": {"var": str(var_name), "value": value}}


def act_emit(message, **fields):
    return {"emit": {"message": str(message), "fields": dict(fields)}}


def act_emit_if(when, message, **fields):
    return {"emit_if": {"when": when, "message": str(message), "fields": dict(fields)}}


def act_arm(timer_name, delay_ms):
    return {"arm": {"timer": str(timer_name), "delay_ms": delay_ms}}


def act_arm_if(when, timer_name, delay_ms):
    return {"arm_if": {"when": when, "timer": str(timer_name), "delay_ms": delay_ms}}


def act_cancel(timer_name):
    return {"cancel": str(timer_name)}


def act_cancel_if(when, timer_name):
    return {"cancel_if": {"when": when, "timer": str(timer_name)}}


def rule(rid, from_state, to_state, event, guard, actions, reqs):
    return {
        "id": str(rid),
        "from": str(from_state),
        "to": str(to_state),
        "event": str(event),
        "guard": guard,
        "actions": list(actions),
        "requirements": list(reqs),
    }


def inv(iid, assert_expr, reqs):
    return {
        "id": str(iid),
        "assert": assert_expr,
        "requirements": list(reqs),
    }


def validate_and_dump(model_dict, path):
    """Validate Protocol IR 0.6 + c99 admission and write canonical formatted JSON."""
    validate(model_dict)
    admit(model_dict)
    out = Path(path)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(model_dict, indent=2) + "\n", encoding="utf-8")
    return out
