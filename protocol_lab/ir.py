"""A typed, deliberately small EFSM IR. No eval or embedded host code."""
import copy
import json
from fractions import Fraction
from math import gcd, ceil
from pathlib import Path

MOD = 1 << 32
HALF = MOD // 2
POST_SEMANTICS = "flat-efsm-atomic-ordered-post-target-v2"
CLOCK_SEMANTICS = "flat-efsm-atomic-ordered-clock-v3"
POST_SEMANTICS_VERSIONS = (POST_SEMANTICS, CLOCK_SEMANTICS)
DATA_VERSIONS = ("0.2", "0.3", "0.4", "0.5", "0.6")
WIRE_OPS = {"bytes_pack8_mod", "bytes_pack16be_mod", "bytes_internet_checksum16"}
READ_OPS = {"bytes_at_or_zero"}
WORD32_OPS = {"bytes_pack32be_mod"}
TYPES = ("bool", "int", "seq32", "string", "bytes", "rational")
RAT_OPS = {"rat_from_int", "rat_add", "rat_sub", "rat_scale", "rat_abs", "rat_le", "rat_ceil"}
DATA_OPS = {"sub", "min", "ite", "bytes_len", "bytes_concat", "bytes_slice",
            "seq_distance", "seq_comparable", "seq_lt", "seq_le"}


class ModelError(ValueError):
    pass


class Uncovered(ModelError):
    """The model has no applicable rule; this is not a protocol verdict."""


class Conflict(ModelError):
    pass


def require(condition, message):
    if not condition:
        raise ModelError(message)


def rational_value(value):
    return {"n": value.numerator, "d": value.denominator}


def fraction(value):
    return Fraction(value["n"], value["d"])


def value_ok(value, kind):
    return {
        "bool": lambda: type(value) is bool,
        "int": lambda: type(value) is int,
        "seq32": lambda: type(value) is int and 0 <= value < MOD,
        "string": lambda: type(value) is str,
        "rational": lambda: type(value) is dict and set(value) == {"n", "d"}
            and type(value["n"]) is int and type(value["d"]) is int and value["d"] > 0
            and gcd(value["n"], value["d"]) == 1,
        "bytes": lambda: type(value) is list and all(type(x) is int and 0 <= x <= 255 for x in value),
    }.get(kind, lambda: False)()


def infer(expr, model, event=None):
    if type(expr) is bool:
        return "bool"
    if type(expr) is int:
        return "int"
    if type(expr) is str:
        return "string"
    require(type(expr) is dict, f"Invalid expression: {expr!r}")
    if set(expr) == {"seq"}:
        require(value_ok(expr["seq"], "seq32"), "Invalid seq32 literal")
        return "seq32"
    if set(expr) == {"clock_ms"}:
        require(expr["clock_ms"] is True and model.get("semantics") == CLOCK_SEMANTICS, "Clock requires clock-v3 semantics")
        return "int"
    if set(expr) == {"rat"}:
        require(model.get("ir_version") == "0.3", "Rational values require IR 0.3")
        require(type(expr["rat"]) is list and len(expr["rat"]) == 2
                and value_ok({"n": expr["rat"][0], "d": expr["rat"][1]}, "rational"), "Bad rational literal")
        return "rational"
    if set(expr) == {"bytes"}:
        require(model.get("ir_version") in DATA_VERSIONS, "bytes requires IR 0.2")
        require(value_ok(expr["bytes"], "bytes"), "Invalid bytes literal")
        return "bytes"
    if set(expr) == {"var"}:
        require(expr["var"] in model["variables"], "Unknown variable")
        return model["variables"][expr["var"]]["type"]
    if set(expr) == {"event"}:
        fields = model["events"].get(event, {}).get("fields", {})
        require(expr["event"] in fields, f"Unknown event field: {expr}")
        return fields[expr["event"]]
    if set(expr) == {"state"}:
        require(expr["state"] in model["states"], "Unknown state")
        return "bool"
    if set(expr) == {"timer_active"}:
        require(expr["timer_active"] in model["timers"], "Unknown timer")
        return "bool"
    require(set(expr) == {"op", "args"} and type(expr["args"]) is list,
            "Unsupported expression shape")
    op, args = expr["op"], expr["args"]
    require(op not in WIRE_OPS or model.get("ir_version") in ("0.4","0.5","0.6"), "Wire arithmetic requires IR 0.4/0.5/0.6")
    require(op not in READ_OPS or model.get("ir_version") in ("0.5","0.6"), "Byte access requires IR 0.5/0.6")
    require(op not in WORD32_OPS or model.get("ir_version") == "0.6", "Word32 packing requires IR 0.6")
    require(op not in DATA_OPS or model.get("ir_version") in DATA_VERSIONS, "Data operators require IR 0.2")
    require(op not in RAT_OPS or model.get("ir_version") == "0.3", "Rational operators require IR 0.3")
    types = [infer(x, model, event) for x in args]
    if op == "rat_scale":
        require(len(args) == 2 and type(args[1]) is dict and set(args[1]) == {"rat"}, "Rational scale requires a literal coefficient")
    if op == "ite":
        require(len(types) == 3 and types[0] == "bool" and types[1] == types[2], "Conditional type mismatch")
        return types[1]
    if op in ("eq", "ne"):
        require(len(types) == 2 and types[0] == types[1], "Equality type mismatch")
        return "bool"
    if op in ("and", "or", "implies", "not"):
        arity = 1 if op == "not" else 2
        require(len(types) == arity and all(t == "bool" for t in types), "Boolean type mismatch")
        return "bool"
    signatures = {
        "rat_from_int": (["int"], "rational"),
        "rat_add": (["rational", "rational"], "rational"),
        "rat_sub": (["rational", "rational"], "rational"),
        "rat_scale": (["rational", "rational"], "rational"),
        "rat_abs": (["rational"], "rational"),
        "rat_le": (["rational", "rational"], "bool"),
        "rat_ceil": (["rational"], "int"),
        "add": (["int", "int"], "int"),
        "mul": (["int", "int"], "int"),
        "le": (["int", "int"], "bool"),
        "ge": (["int", "int"], "bool"),
        "seq_add": (["seq32", "int"], "seq32"),
        "sub": (["int", "int"], "int"),
        "min": (["int", "int"], "int"),
        "bytes_len": (["bytes"], "int"),
        "bytes_concat": (["bytes", "bytes"], "bytes"),
        "bytes_slice": (["bytes", "int", "int"], "bytes"),
        "bytes_pack8_mod": (["int"], "bytes"),
        "bytes_pack16be_mod": (["int"], "bytes"),
        "bytes_pack32be_mod": (["int"], "bytes"),
        "bytes_internet_checksum16": (["bytes"], "int"),
        "bytes_at_or_zero": (["bytes", "int"], "int"),
        "seq_distance": (["seq32", "seq32"], "int"),
        "seq_comparable": (["seq32", "seq32"], "bool"),
        "seq_lt": (["seq32", "seq32"], "bool"),
        "seq_le": (["seq32", "seq32"], "bool"),
    }
    require(op in signatures, f"Unsupported operator: {op}")
    inputs, output = signatures[op]
    require(types == inputs, f"{op} expects {inputs}, got {types}")
    return output


def internet_checksum16(data):
    """Pure arithmetic: RFC1071 section1, big-endian pairs, final odd-byte zero.

    This never applies UDP absent-checksum or zero-to-FFFF transmit policy.
    """
    words=[(data[i]<<8)+(data[i+1]if i+1<len(data)else 0)for i in range(0,len(data),2)]
    total=sum(words)
    while total>>16:total=(total&65535)+(total>>16)
    return 65535-total


def evaluate(expr, machine, event=None):
    if type(expr) is not dict:
        return expr
    if "clock_ms" in expr:
        return machine.now_ms
    if "rat" in expr:
        return {"n": expr["rat"][0], "d": expr["rat"][1]}
    if "seq" in expr:
        return expr["seq"]
    if "bytes" in expr:
        return expr["bytes"].copy()
    if "var" in expr:
        return machine.values[expr["var"]]
    if "event" in expr:
        return event["fields"][expr["event"]]
    if "state" in expr:
        return machine.state == expr["state"]
    if "timer_active" in expr:
        return expr["timer_active"] in machine.timers
    args = [evaluate(x, machine, event) for x in expr["args"]]
    return {
        "rat_from_int": lambda a: {"n": a, "d": 1},
        "rat_add": lambda a, b: rational_value(fraction(a) + fraction(b)),
        "rat_sub": lambda a, b: rational_value(fraction(a) - fraction(b)),
        "rat_scale": lambda a, b: rational_value(fraction(a) * fraction(b)),
        "rat_abs": lambda a: rational_value(abs(fraction(a))),
        "rat_le": lambda a, b: fraction(a) <= fraction(b),
        "rat_ceil": lambda a: ceil(fraction(a)),
        "eq": lambda a, b: a == b,
        "ne": lambda a, b: a != b,
        "and": lambda a, b: a and b,
        "or": lambda a, b: a or b,
        "not": lambda a: not a,
        "implies": lambda a, b: not a or b,
        "add": lambda a, b: a + b,
        "mul": lambda a, b: a * b,
        "le": lambda a, b: a <= b,
        "ge": lambda a, b: a >= b,
        "seq_add": lambda a, b: (a + b) % MOD,
        "sub": lambda a, b: a - b,
        "min": min,
        "ite": lambda condition, yes, no: yes if condition else no,
        "bytes_len": len,
        "bytes_concat": lambda a, b: a + b,
        "bytes_pack8_mod": lambda n: [n%256],
        "bytes_pack16be_mod": lambda n: [(n%65536)//256,n%256],
        "bytes_pack32be_mod": lambda n: [(n%MOD)//(1<<shift)%256 for shift in (24,16,8,0)],
        "bytes_internet_checksum16": internet_checksum16,
        "bytes_at_or_zero": lambda a, i: a[i] if 0 <= i < len(a) else 0,
        # Total truncating slice: offset and count are clamped independently.
        "bytes_slice": lambda a, offset, count: a[max(0, offset):max(0, offset) + max(0, count)],
        "seq_distance": lambda a, b: (b - a) % MOD,
        "seq_comparable": lambda a, b: (b - a) % MOD != HALF,
        "seq_lt": lambda a, b: 0 < (b - a) % MOD < HALF,
        "seq_le": lambda a, b: (b - a) % MOD < HALF,
    }[expr["op"]](*args)


def validate(model):
    require("extends" not in model, "Resolve model extension with load() before validation")
    require(model.get("ir_version") in ("0.1", "0.2", "0.3", "0.4", "0.5", "0.6"), "Unsupported IR version")
    require(model.get("ir_version") not in ("0.4","0.5","0.6") or model.get("semantics") == "flat-efsm-atomic-ordered-v1", "IR 0.4/0.5/0.6 currently requires atomic ordered v1")
    require(model.get("semantics") in ("flat-efsm-atomic-ordered-v1", *POST_SEMANTICS_VERSIONS), "Unsupported semantics")
    require(model.get("semantics") != CLOCK_SEMANTICS or model["ir_version"] == "0.3", "Clock-v3 requires IR 0.3")
    states = model["states"]
    require(len(states) == len(set(states)), "Duplicate states")
    require(model["initial_state"] in states, "Unknown initial state")
    requirements = model["requirements"]
    require(bool(requirements), "Requirements are required")
    for rid, req in requirements.items():
        require(bool(req.get("source")) and bool(req.get("interpretation")), f"Untraceable requirement {rid}")
    for name, var in model["variables"].items():
        require(var["type"] != "bytes" or model["ir_version"] in DATA_VERSIONS, "bytes requires IR 0.2")
        require(var["type"] != "rational" or model["ir_version"] == "0.3", "Rational values require IR 0.3")
        require(value_ok(var["initial"], var["type"]), f"Bad initial value: {name}")
    for name, event in model["events"].items():
        require(event["origin"] in ("application", "network", "timer"), f"Bad origin: {name}")
        require(all(t in TYPES and (t != "bytes" or model["ir_version"] in DATA_VERSIONS) and (t != "rational" or model["ir_version"] == "0.3") for t in event["fields"].values()), "Bad event field type")
    for message in model["messages"].values():
        require(all(t in TYPES and (t != "bytes" or model["ir_version"] in DATA_VERSIONS) and (t != "rational" or model["ir_version"] == "0.3") for t in message["fields"].values()), "Bad message field type")
    timer_events = []
    for timer in model["timers"].values():
        event = model["events"].get(timer["event"], {})
        require(event.get("origin") == "timer" and event.get("fields") == {}, "Bad timer event")
        timer_events.append(timer["event"])
    require(len(timer_events) == len(set(timer_events)), "Timers must have distinct expiry events")
    ids = set()
    for rule in model["transitions"]:
        require(rule["id"] not in ids, "Duplicate transition ID")
        ids.add(rule["id"])
        require(rule["from"] in states and rule["to"] in states, "Unknown transition state")
        if "target_cases" in rule:
            require(model["semantics"] in POST_SEMANTICS_VERSIONS and model["ir_version"] in DATA_VERSIONS, "Post targets require versioned post-target semantics")
            require(type(rule["target_cases"]) is list and bool(rule["target_cases"]), "Bad post target list")
            for case in rule["target_cases"]:
                require(type(case) is dict and set(case) == {"when", "to"}, "Bad post target case")
                require(case["to"] in states, "Unknown post target state")
                require(infer(case["when"], model, rule["event"]) == "bool", "Post target requires bool")
        require(rule["event"] in model["events"], "Unknown transition event")
        require(bool(rule["requirements"]) and all(r in requirements for r in rule["requirements"]), "Unknown requirement")
        require(infer(rule["guard"], model, rule["event"]) == "bool", "Non-boolean guard")
        for action in rule["actions"]:
            require(len(action) == 1, "An action must have one operator")
            kind, arg = next(iter(action.items()))
            if kind == "set":
                require(arg["var"] in model["variables"], "Unknown assignment target")
                require(infer(arg["value"], model, rule["event"]) == model["variables"][arg["var"]]["type"], "Assignment type mismatch")
            elif kind in ("emit", "emit_if"):
                if kind == "emit_if":
                    require(model["semantics"] in POST_SEMANTICS_VERSIONS and model["ir_version"] in DATA_VERSIONS, "Conditional emit requires versioned post-target semantics")
                    require(set(arg) == {"when", "message", "fields"}, "Bad conditional emit shape")
                    require(infer(arg["when"], model, rule["event"]) == "bool", "Conditional emit requires bool")
                schema = model["messages"].get(arg["message"])
                require(schema is not None, "Unknown message")
                require(set(arg["fields"]) == set(schema["fields"]), "Message fields mismatch")
                for field, expr in arg["fields"].items():
                    require(infer(expr, model, rule["event"]) == schema["fields"][field], f"Message field type mismatch: {field}")
            elif kind in ("arm", "arm_if"):
                if kind == "arm_if":
                    require(model["ir_version"] in DATA_VERSIONS, "Conditional timers require IR 0.2")
                    require(set(arg) == {"when", "timer", "delay_ms"}, "Bad conditional arm shape")
                    require(infer(arg["when"], model, rule["event"]) == "bool", "Conditional timer requires bool")
                require(arg["timer"] in model["timers"], "Unknown timer")
                require(infer(arg["delay_ms"], model, rule["event"]) == "int", "Bad timer duration type")
            elif kind == "cancel":
                require(arg in model["timers"], "Unknown timer")
            elif kind == "cancel_if":
                require(model["ir_version"] in DATA_VERSIONS, "Conditional timers require IR 0.2")
                require(set(arg) == {"when", "timer"}, "Bad conditional cancel shape")
                require(arg["timer"] in model["timers"], "Unknown timer")
                require(infer(arg["when"], model, rule["event"]) == "bool", "Conditional timer requires bool")
            else:
                raise ModelError(f"Unsupported action: {kind}")
    invariant_ids = set()
    for inv in model["invariants"]:
        require(inv["id"] not in invariant_ids, "Duplicate invariant ID")
        invariant_ids.add(inv["id"])
        require(infer(inv["assert"], model) == "bool", "Non-boolean invariant")
        require(bool(inv["requirements"]) and all(r in requirements for r in inv["requirements"]), "Unknown invariant requirement")
    return model


def model_files(path, seen=()):
    """Enumerate declarative base files; used by evidence hashing as well."""
    path = Path(path).resolve()
    require(path not in seen, "Cyclic model extension")
    raw = json.loads(path.read_text())
    files = [path]
    if "extends" in raw:
        require(type(raw["extends"]) is str, "Invalid model base path")
        require(not Path(raw["extends"]).is_absolute(), "Model base path must be relative")
        base = (path.parent / raw["extends"]).resolve()
        require(base.is_relative_to(path.parent), "Model base escapes model directory")
        files += model_files(base, (*seen, path))
    return files


def load(path):
    files = model_files(path)
    model = json.loads(files[-1].read_text())
    for source in reversed(files[:-1]):
        overlay = json.loads(source.read_text())
        require(overlay.get("ir_version") in DATA_VERSIONS, "Model extension requires a data IR version")
        for group in ("transitions", "invariants"):
            removals = overlay.get("remove_" + group, [])
            require(type(removals) is list and len(removals) == len(set(removals)), "Invalid removal IDs")
            require(set(removals) <= {r["id"] for r in model[group]}, f"Unknown base {group} removal")
            model[group] = [r for r in model[group] if r["id"] not in removals] + overlay.get(group, [])
        amended = set()
        for amendment in overlay.get("amend_transitions", []):
            require(set(amendment) <= {"id", "and_guard", "guard", "prepend_actions", "append_actions", "edit_actions", "add_requirements"}, "Unsupported transition amendment")
            rid = amendment["id"]
            require(rid not in amended, "Duplicate transition amendment")
            amended.add(rid)
            matches = [r for r in model["transitions"] if r["id"] == rid]
            require(len(matches) == 1, "Unknown/ambiguous transition amendment")
            rule = matches[0]
            require(not ("guard" in amendment and "and_guard" in amendment), "Ambiguous guard amendment")
            if "guard" in amendment:
                rule["guard"] = amendment["guard"]
            if "and_guard" in amendment:
                rule["guard"] = {"op": "and", "args": [rule["guard"], amendment["and_guard"]]}
            for edit in amendment.get("edit_actions", []):
                require(set(edit) == {"at", "expected", "with"}, "Bad action edit shape")
                index = edit["at"]
                require(type(index) is int and 0 <= index < len(rule["actions"]), "Action edit index out of range")
                require(rule["actions"][index] == edit["expected"], "Action edit anchor changed")
                require(type(edit["with"]) is list, "Action edit replacement must be a list")
                rule["actions"][index:index+1] = edit["with"]
            rule["actions"] = amendment.get("prepend_actions", []) + rule["actions"] + amendment.get("append_actions", [])
            added = amendment.get("add_requirements", [])
            require(type(added) is list and len(added) == len(set(added))
                    and not set(added).intersection(rule["requirements"]), "Duplicate added requirement")
            rule["requirements"] += added
        for key, value in overlay.items():
            if key in ("extends", "transitions", "invariants", "remove_transitions", "remove_invariants", "amend_transitions"):
                continue
            if key in ("requirements", "variables", "events", "messages", "timers"):
                model[key].update(value)
            else:
                model[key] = value
    return validate(model)


class Machine:
    def __init__(self, model, initial=None):
        self.model = validate(copy.deepcopy(model))
        self.state = model["initial_state"]
        self.values = {k: copy.deepcopy(v["initial"]) for k, v in self.model["variables"].items()}
        for key, value in (initial or {}).items():
            require(key in model["variables"], f"Unknown initial variable {key}")
            require(value_ok(value, model["variables"][key]["type"]), f"Bad initial variable {key}")
            self.values[key] = copy.deepcopy(value)
        self.timers = {}
        self.now_ms = 0
        self.trace = []
        self.check_invariants()

    def snapshot(self):
        return {"state": self.state, "variables": copy.deepcopy(self.values), "timers": self.timers.copy()}

    def check_invariants(self):
        for key, var in self.model["variables"].items():
            require(value_ok(self.values[key], var["type"]), f"Variable type violation: {key}")
        for inv in self.model["invariants"]:
            require(evaluate(inv["assert"], self), f"Invariant failed: {inv['id']}")

    def _fire(self, name, fields, timer=None):
        event = {"name": name, "fields": fields}
        schema = self.model["events"].get(name)
        require(schema is not None, f"Unknown event {name}")
        require(set(fields) == set(schema["fields"]), f"Event field mismatch: {name}")
        for key, kind in schema["fields"].items():
            require(value_ok(fields[key], kind), f"Bad event value: {key}")
        matches = [r for r in self.model["transitions"] if r["from"] == self.state and r["event"] == name and evaluate(r["guard"], self, event)]
        if not matches:
            raise Uncovered(f"No transition: state={self.state}, event={event}")
        if len(matches) > 1:
            raise Conflict(f"Overlapping rules: {[r['id'] for r in matches]}")
        rule = matches[0]
        before = self.snapshot()
        if timer:
            del self.timers[timer]
        emitted = []
        for action in rule["actions"]:
            kind, arg = next(iter(action.items()))
            if kind == "set":
                self.values[arg["var"]] = copy.deepcopy(evaluate(arg["value"], self, event))
            elif kind in ("emit", "emit_if"):
                if kind == "emit_if" and not evaluate(arg["when"], self, event):
                    continue
                emitted.append({"message": arg["message"], "fields": {k: copy.deepcopy(evaluate(v, self, event)) for k, v in arg["fields"].items()}})
            elif kind == "cancel":
                self.timers.pop(arg, None)
            elif kind == "cancel_if":
                if evaluate(arg["when"], self, event):
                    self.timers.pop(arg["timer"], None)
            elif kind in ("arm", "arm_if"):
                if kind == "arm_if" and not evaluate(arg["when"], self, event):
                    continue
                delay = evaluate(arg["delay_ms"], self, event)
                require(type(delay) is int and delay > 0, "Timer duration must be positive")
                self.timers[arg["timer"]] = self.now_ms + delay
        target = rule["to"]
        for case in rule.get("target_cases", []):
            if evaluate(case["when"], self, event):
                target = case["to"]
                break
        self.state = target
        record = {"event_id": f"e{len(self.trace)+1:04d}", "time_ms": self.now_ms,
                  "event": event, "transition": rule["id"], "requirements": rule["requirements"],
                  "before": before, "after": self.snapshot(), "emitted": emitted}
        self.trace.append(record)
        self.check_invariants()

    def _fire_next_timer(self, time_ms):
        require(type(time_ms) is int and time_ms >= self.now_ms, "Time must be monotonic integer milliseconds")
        require(bool(self.timers), "No active timer")
        timer = min(self.timers, key=lambda x: (self.timers[x], x))
        require(self.timers[timer] == time_ms, "Must fire the next timer at its exact deadline")
        self.now_ms = time_ms
        self._fire(self.model["timers"][timer]["event"], {}, timer)

    def step_timer(self, time_ms):
        """Commit one scheduled transition, including a prefix of a tied batch.

        The caller supplies only time; the scheduler chooses the actual earliest
        timer. Public dispatch still forbids injecting timer event names.
        """
        candidate = copy.deepcopy(self)
        candidate._fire_next_timer(time_ms)
        candidate.check_invariants()
        self.__dict__.update(candidate.__dict__)

    def _advance(self, time_ms):
        require(type(time_ms) is int and time_ms >= self.now_ms, "Time must be monotonic integer milliseconds")
        while self.timers and min(self.timers.values()) <= time_ms:
            self._fire_next_timer(min(self.timers.values()))
        self.now_ms = time_ms

    def dispatch(self, name, fields=None, time_ms=None):
        # Commit a complete operation only after guards, actions and invariants pass.
        # Failed operations leave the caller's machine untouched.
        candidate = copy.deepcopy(self)
        require(name in self.model["events"], f"Unknown event {name}")
        require(self.model["events"][name]["origin"] != "timer", "Timer events cannot be injected")
        candidate._advance(self.now_ms if time_ms is None else time_ms)
        candidate._fire(name, copy.deepcopy(fields or {}))
        self.__dict__.update(candidate.__dict__)

    def tick(self, time_ms):
        candidate = copy.deepcopy(self)
        candidate._advance(time_ms)
        candidate.check_invariants()
        self.__dict__.update(candidate.__dict__)
