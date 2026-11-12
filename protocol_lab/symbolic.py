"""Independent bounded symbolic semantics for IR 0.1/0.2/0.3/0.4/0.5/0.6 (Z3 optional).

No call to runtime evaluate/dispatch is used to construct the transition system.
The runtime is invoked only afterwards to cross-check solver witnesses.
"""
import hashlib
import json
from pathlib import Path

from .ir import CLOCK_SEMANTICS, MOD, WIRE_OPS, READ_OPS, WORD32_OPS, Machine, ModelError, infer, require, validate


def model_hash(model):
    return hashlib.sha256(json.dumps(model, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def replay(model, witness):
    try:
        require(type(witness) is dict and type(witness.get("initial")) is dict
                and type(witness.get("steps")) is list, "Malformed witness")
        machine = Machine(model, witness["initial"])
    except ModelError as exc:
        return {"status": "runtime_rejected", "step": "initial", "error": str(exc)}
    compared = 0
    for step in witness["steps"]:
        try:
            require(type(step) is dict and {"at_ms", "event", "origin", "transition", "fields", "after", "emitted"} <= set(step), "Malformed witness step")
            require(type(step["at_ms"]) is int and type(step["fields"]) is dict
                    and type(step["after"]) is dict and type(step["emitted"]) is list,
                    "Malformed witness step values")
            trace_size = len(machine.trace)
            if step["origin"] == "clock":
                require(model["semantics"] == CLOCK_SEMANTICS and step["event"] is None
                        and step["transition"] == "@clock_advance" and step["fields"] == {},
                        "Invalid clock witness metadata")
                machine.tick(step["at_ms"])
                if (len(machine.trace) != trace_size or machine.now_ms != step["at_ms"]
                        or machine.snapshot() != step["after"] or step["emitted"] != []):
                    return {"status": "semantic_mismatch", "step": compared, "runtime": machine.snapshot(), "symbolic": step["after"]}
                compared += 1
                continue
            require(type(step["event"]) is str and type(step["transition"]) is str,
                    "Malformed witness event metadata")
            schema = model["events"].get(step["event"])
            require(schema is not None and schema["origin"] == step["origin"],
                    "Witness event origin mismatch")
            if step["origin"] == "timer":
                require(step["fields"] == {}, "Timer witness fields must be empty")
                machine.step_timer(step["at_ms"])
            else:
                machine.dispatch(step["event"], step["fields"], step["at_ms"])
        except ModelError as exc:
            return {"status": "runtime_rejected", "step": compared, "error": str(exc)}
        if len(machine.trace) != trace_size + 1:
            return {"status": "semantic_mismatch", "step": compared, "reason": "Witness omitted scheduled transitions"}
        row = machine.trace[-1]
        if (row["time_ms"] != step["at_ms"]
                or row["event"] != {"name": step["event"], "fields": step["fields"]}
                or row["transition"] != step["transition"]
                or machine.snapshot() != step["after"] or row["emitted"] != step["emitted"]):
            return {"status": "semantic_mismatch", "step": compared,
                    "runtime": machine.snapshot(), "symbolic": step["after"]}
        compared += 1
    return {"status": "match", "compared_steps": compared}


def encode_trace(model, trace, **encoding_options):
    """Constrain inputs/rule choices, without assuming poststates or invariants."""
    require(bool(trace), "Cannot cross-check an empty trace")
    # Initial overrides are concrete inputs, not assumed safety properties.
    initial = trace[0]["before"]["variables"]
    overrides = [n for n, v in model["variables"].items() if initial[n] != v["initial"]]
    choices = []
    for row in trace:
        indices = [j for j, r in enumerate(model["transitions"]) if r["id"] == row["transition"]]
        require(len(indices) == 1, "Trace references unknown transition")
        choices.append(indices[0])
    enc = Encoding(model, len(trace), overrides, fixed_choices=choices, **encoding_options)
    z = enc.z
    fixed = []
    for name, value in initial.items():
        fixed.append((enc.frames[0]["values"][name], enc.literal(value, model["variables"][name]["type"])))
        enc.solver.add(enc.frames[0]["values"][name] == enc.literal(value, model["variables"][name]["type"]))
    for i, row in enumerate(trace):
        indices = [j for j, r in enumerate(model["transitions"]) if r["id"] == row["transition"]]
        require(len(indices) == 1, "Trace references unknown transition")
        require(model["transitions"][indices[0]]["event"] == row["event"]["name"], "Trace event/transition mismatch")
        fixed += [(z.Int(f"choice_{i}"), z.IntVal(indices[0])),
                  (enc.frames[i+1]["now"], z.IntVal(row["time_ms"]))]
        enc.solver.add(z.Int(f"choice_{i}") == indices[0], enc.frames[i+1]["now"] == row["time_ms"])
        schema = model["events"][row["event"]["name"]]["fields"]
        require(set(row["event"]["fields"]) == set(schema), "Trace event fields mismatch")
        for name, value in row["event"]["fields"].items():
            literal = enc.literal(value, schema[name])
            fixed.append((enc.events[i][row["event"]["name"]][name], literal))
            enc.solver.add(enc.events[i][row["event"]["name"]][name] == literal)
    # Exact partial evaluation of the already fixed inputs/rule choices. No
    # reference poststate, invariant or expected output enters these constraints.
    assertions = list(enc.solver.assertions())
    enc.solver = z.Solver()
    enc.solver.set(timeout=10000)
    enc.solver.add(*[z.simplify(z.substitute(assertion, *fixed)) for assertion in assertions])
    enc.solver.add(*[symbol == literal for symbol, literal in fixed])
    return enc


def crosscheck_trace(model, trace, out=None):
    enc = encode_trace(model, trace)
    query = enc.solver.to_smt2()
    if out is not None:
        out = Path(out)
        out.mkdir(parents=True, exist_ok=True)
        (out / "path.smt2").write_text(query)
    answer = enc.solve()
    result = {"backend": "z3-constrained-trace", "scope": "fixed_inputs_and_rule_choices",
              "all_input_safety": "not_claimed", "query_strategy": "exact_fixed_choice_encoding_and_fixed_input_substitution", "steps": len(trace), "query": str(answer),
              "model_semantic_sha256": model_hash(model), "solver_version": enc.z.get_version_string(),
              "smt2_sha256": hashlib.sha256(query.encode()).hexdigest()}
    if answer == enc.z.sat:
        result["witness"] = enc.witness(enc.solver.model())
        result["replay"] = replay(model, result["witness"])
        result["status"] = result["replay"]["status"]
        # Verify the supplied reference trace as well, not only a new replay.
        before = {"state": model["initial_state"], "variables": result["witness"]["initial"], "timers": {}}
        for row, step in zip(trace, result["witness"]["steps"]):
            if (row["before"] != before or row["after"] != step["after"] or row["emitted"] != step["emitted"]
                    or row["event"] != {"name": step["event"], "fields": step["fields"]}
                    or row["time_ms"] != step["at_ms"]):
                result["status"] = "semantic_mismatch"
            before = step["after"]
    elif answer == enc.z.unknown:
        result.update(status="unknown", reason=enc.reason_unknown())
    else:
        result["status"] = "symbolic_rejected_trace"
    if out is not None:
        out = Path(out)
        out.mkdir(parents=True, exist_ok=True)
        (out / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    return result


class Encoding:
    def solve(self):
        """Solver resource failures are inconclusive, never a passing result."""
        self.solver_error = None
        try:
            return self.solver.check()
        except self.z.Z3Exception as exc:
            self.solver_error = str(exc)
            return self.z.unknown

    def reason_unknown(self):
        return self.solver_error or self.solver.reason_unknown()

    def __init__(self, model, depth, symbolic_initials, byte_encoding="sequence", sequence_encoding="bitvector", arbitrary_state=False, fixed_choices=None, solver_preprocess="none"):
        try:
            import z3
        except ImportError as exc:
            raise ModelError("Z3 is missing: install requirements-formal.txt in .venv") from exc
        self.z = z3
        self.model = validate(model)
        require(byte_encoding in ("sequence", "length"), "Unsupported symbolic byte encoding")
        require(solver_preprocess in ("none", "exact-v1"), "Unsupported solver preprocessing plan")
        self.byte_encoding = byte_encoding
        self.solver_preprocess = solver_preprocess
        self.solver_tactics = ("propagate-values", "solve-eqs", "simplify", "smt") if solver_preprocess == "exact-v1" else ()
        self.solver_preprocess_source = "z3.Then(" + ",".join(self.solver_tactics) + ").solver()" if self.solver_tactics else "z3.Solver()"
        if solver_preprocess == "exact-v1":
            require(byte_encoding != "length", "exact-v1 does not support length projection")
        require(sequence_encoding in ("bitvector", "modular-int"), "Unsupported sequence encoding")
        self.sequence_encoding = sequence_encoding
        if byte_encoding == "length":
            require(model["ir_version"] != "0.6", "Length projection does not support IR 0.6")
            self.validate_length_projection()
        require(fixed_choices is None or (type(fixed_choices) is list and len(fixed_choices) == depth
                and all(type(j) is int and 0 <= j < len(model["transitions"]) for j in fixed_choices)),
                "Invalid fixed rule choices")
        self.fixed_choices = fixed_choices
        self.clock_progress = model["semantics"] == CLOCK_SEMANTICS
        self.depth = depth
        self.initials = symbolic_initials
        require(type(depth) is int and 1 <= depth <= 30, "Symbolic depth must be 1..30")
        require(all(n in model["variables"] for n in symbolic_initials), "Unknown symbolic initial variable")
        self.byte_sort = z3.SeqSort(z3.BitVecSort(8)) if byte_encoding == "sequence" else z3.IntSort()
        self.checksum_sum = None
        self._expr_cache = {}
        self._cache_enabled = False
        self._cache_event_name = None
        self.sorts = {"bool": z3.BoolSort(), "int": z3.IntSort(),
                      "seq32": z3.BitVecSort(32) if sequence_encoding == "bitvector" else z3.IntSort(),
                      "string": z3.StringSort(), "bytes": self.byte_sort, "rational": z3.RealSort()}
        self.frames = []
        self.events, self.branches, self.conflicts, self.action_faults, self.enabled = [], [], [], [], []
        self.solver = z3.Then(*self.solver_tactics).solver() if self.solver_tactics else z3.Solver()
        self.solver.set(timeout=10000)
        for i in range(depth + 1):
            self.frames.append({"state": z3.Int(f"state_{i}"), "now": z3.Int(f"now_{i}"),
                "values": {n: z3.Const(f"v_{i}_{n}", self.sorts[v["type"]]) for n, v in model["variables"].items()},
                "active": {n: z3.Bool(f"active_{i}_{n}") for n in model["timers"]},
                "due": {n: z3.Int(f"due_{i}_{n}") for n in model["timers"]}})
        first = self.frames[0]
        if byte_encoding == "length":
            for frame in self.frames:
                self.solver.add(*[frame["values"][n] >= 0 for n, v in model["variables"].items() if v["type"] == "bytes"])
        if sequence_encoding == "modular-int":
            for frame in self.frames:
                for n, v in model["variables"].items():
                    if v["type"] == "seq32":
                        self.solver.add(frame["values"][n] >= 0, frame["values"][n] < MOD)
        if arbitrary_state:
            self.solver.add(first["state"] >= 0, first["state"] < len(model["states"]), first["now"] >= 0)
        else:
            self.solver.add(first["state"] == model["states"].index(model["initial_state"]), first["now"] == 0)
        for n, var in model["variables"].items():
            if n not in symbolic_initials:
                self.solver.add(first["values"][n] == self.literal(var["initial"], var["type"]))
        for n in model["timers"]:
            if arbitrary_state:
                self.solver.add(z3.Implies(first["active"][n], first["due"][n] >= first["now"]))
            else:
                self.solver.add(z3.Not(first["active"][n]), first["due"][n] == 0)
        for i in range(depth):
            self.encode_step(i)

    def validate_length_projection(self):
        """Reject every content observation; do not approximate bytes equality."""
        def visit(expr, event=None):
            if type(expr) is not dict or "op" not in expr:
                return
            require(expr['op']not in WIRE_OPS|READ_OPS|WORD32_OPS,"Length projection does not support wire arithmetic/byte access")
            if expr["op"] in ("eq", "ne"):
                require(infer(expr["args"][0], self.model, event) != "bytes",
                        "Length projection does not support byte-content equality")
            for arg in expr["args"]:
                visit(arg, event)
        for rule in self.model["transitions"]:
            visit(rule["guard"], rule["event"])
            for case in rule.get("target_cases", []):
                visit(case["when"], rule["event"])
            for action in rule["actions"]:
                kind, arg = next(iter(action.items()))
                if kind == "set":
                    visit(arg["value"], rule["event"])
                elif kind in ("arm", "arm_if"):
                    visit(arg["delay_ms"], rule["event"])
                    if kind == "arm_if":
                        visit(arg["when"], rule["event"])
                elif kind == "cancel_if":
                    visit(arg["when"], rule["event"])
                elif kind in ("emit", "emit_if"):
                    if kind == "emit_if":
                        visit(arg["when"], rule["event"])
                    for expr in arg["fields"].values():
                        visit(expr, rule["event"])
        for inv in self.model["invariants"]:
            visit(inv["assert"])

    def literal(self, value, kind=None):
        z = self.z
        if kind == "rational":
            return z.RealVal(f"{value['n']}/{value['d']}")
        if kind == "seq32":
            return z.BitVecVal(value, 32) if self.sequence_encoding == "bitvector" else z.IntVal(value)
        if kind == "bytes":
            if self.byte_encoding == "length":
                return z.IntVal(len(value))
            units = [z.Unit(z.BitVecVal(v, 8)) for v in value]
            return z.Concat(*units) if len(units) > 1 else units[0] if units else z.Empty(self.byte_sort)
        if type(value) is bool:
            return z.BoolVal(value)
        if type(value) is int:
            return z.IntVal(value)
        return z.StringVal(value)

    def expr(self, value, frame, fields=None):
        if not self._cache_enabled:
            return self._expr_uncached(value, frame, fields)
        if self._contains_checksum(value):
            return self._expr_uncached(value, frame, fields)
        key = (self._cache_event_name, json.dumps(value, sort_keys=True, separators=(",", ":")))
        if key not in self._expr_cache:
            self._expr_cache[key] = self._expr_uncached(value, frame, fields)
        return self._expr_cache[key]

    def _contains_checksum(self, value):
        if type(value) is not dict:
            return False
        if value.get("op") == "bytes_internet_checksum16":
            return True
        for arg in value.get("args", []):
            if self._contains_checksum(arg):
                return True
        return False

    def _expr_uncached(self, value, frame, fields=None):
        z = self.z
        if type(value) is not dict:
            return self.literal(value)
        if "clock_ms" in value:
            return frame["now"]
        if "rat" in value:
            return self.literal({"n": value["rat"][0], "d": value["rat"][1]}, "rational")
        if "seq" in value:
            return self.literal(value["seq"], "seq32")
        if "bytes" in value:
            return self.literal(value["bytes"], "bytes")
        if "var" in value:
            return frame["values"][value["var"]]
        if "event" in value:
            return fields[value["event"]]
        if "state" in value:
            return frame["state"] == self.model["states"].index(value["state"])
        if "timer_active" in value:
            return frame["active"][value["timer_active"]]
        args = [self.expr(v, frame, fields) for v in value["args"]]
        operators = {"rat_from_int": z.ToReal,
                "rat_add": lambda a, b: a+b, "rat_sub": lambda a, b: a-b,
                "rat_scale": lambda a, b: a*b, "rat_abs": lambda a: z.If(a >= 0, a, -a),
                "rat_le": lambda a, b: a <= b, "rat_ceil": lambda a: -z.ToInt(-a),
                "eq": lambda a, b: a == b, "ne": lambda a, b: a != b,
                "and": z.And, "or": z.Or, "not": z.Not, "implies": z.Implies,
                "add": lambda a, b: a+b, "mul": lambda a, b: a*b,
                "le": lambda a, b: a <= b, "ge": lambda a, b: a >= b,
                "seq_add": lambda a, b: a + z.Int2BV(b, 32),
                "sub": lambda a, b: a - b,
                "min": lambda a, b: z.If(a <= b, a, b),
                "ite": z.If,
                "bytes_len": z.Length,
                "bytes_concat": z.Concat,
                "bytes_pack8_mod": lambda n: z.Unit(z.Int2BV(n,8)),
                "bytes_pack16be_mod": lambda n: z.Concat(z.Unit(z.Extract(15,8,z.Int2BV(n,16))),z.Unit(z.Extract(7,0,z.Int2BV(n,16)))),
                "bytes_pack32be_mod": lambda n: z.Concat(*[z.Unit(z.Extract(shift+7,shift,z.Int2BV(n,32)))for shift in (24,16,8,0)]),
                "bytes_internet_checksum16": self.checksum_expr,
                "bytes_at_or_zero": lambda a,i: z.If(z.And(i>=0,i<z.Length(a)),z.BV2Int(a[i],is_signed=False),0),
                "bytes_slice": lambda a, offset, count: z.SubSeq(a, z.If(offset < 0, 0, offset), z.If(count < 0, 0, count)),
                "seq_distance": lambda a, b: z.BV2Int(b - a, is_signed=False),
                "seq_comparable": lambda a, b: b - a != z.BitVecVal(1 << 31, 32),
                "seq_lt": lambda a, b: z.And(a != b, z.ULT(b - a, z.BitVecVal(1 << 31, 32))),
                "seq_le": lambda a, b: z.ULT(b - a, z.BitVecVal(1 << 31, 32))}
        if self.byte_encoding == "length":
            def slice_length(length, offset, count):
                start = z.If(offset < 0, 0, offset)
                size = z.If(count < 0, 0, count)
                remaining = z.If(length > start, length - start, 0)
                return z.If(size < remaining, size, remaining)
            operators.update(bytes_len=lambda a: a, bytes_concat=lambda a, b: a+b,
                             bytes_slice=slice_length)
        if self.sequence_encoding == "modular-int":
            operators.update(seq_add=lambda a, b: (a+b) % MOD,
                             seq_distance=lambda a, b: (b-a) % MOD,
                             seq_comparable=lambda a, b: (b-a) % MOD != MOD//2,
                             seq_lt=lambda a, b: z.And((b-a) % MOD > 0, (b-a) % MOD < MOD//2),
                             seq_le=lambda a, b: (b-a) % MOD < MOD//2)
        require(value["op"] in operators, f"Unsupported symbolic operator: {value['op']}")
        return operators[value["op"]](*args)

    def checksum_expr(self, sequence):
        """Exact recursive BV sequence fold, independent of runtime arithmetic.

        No byte-length cut-off or concrete reference evaluation is substituted.
        The solver may return UNKNOWN for general recursive obligations.
        """
        z=self.z
        require(self.byte_encoding=='sequence','Checksum needs exact byte content')
        if self.checksum_sum is None:
            name='ir4_ones_sum16_'+str(z.FreshInt('checksum_instance'))
            f=z.RecFunction(name,self.byte_sort,z.BitVecSort(16))
            s=z.Const(name+'_input',self.byte_sort);length=z.Length(s)
            word=z.Concat(s[0],z.If(length>1,s[1],z.BitVecVal(0,8)))
            rest=f(z.SubSeq(s,2,z.If(length>2,length-2,0)))
            wide=z.ZeroExt(1,word)+z.ZeroExt(1,rest)
            folded=z.Extract(15,0,wide)+z.ZeroExt(15,z.Extract(16,16,wide))
            z.RecAddDefinition(f,s,z.If(length==0,z.BitVecVal(0,16),folded))
            self.checksum_sum=f
        return z.BV2Int(~self.checksum_sum(sequence),is_signed=False)

    def encode_step(self, index):
        z, m = self.z, self.model
        old, new = self.frames[index:index+2]
        fields = {name: {n: z.Const(f"input_{index}_{name}_{n}", self.sorts[kind]) for n, kind in spec["fields"].items()}
                  for name, spec in m["events"].items()}
        self.events.append(fields)
        if self.byte_encoding == "length":
            self.solver.add(*[fields[name][n] >= 0 for name, spec in m["events"].items()
                              for n, kind in spec["fields"].items() if kind == "bytes"])
        if self.sequence_encoding == "modular-int":
            for name, spec in m["events"].items():
                for n, kind in spec["fields"].items():
                    if kind == "seq32":
                        self.solver.add(fields[name][n] >= 0, fields[name][n] < MOD)
        choice = z.Int(f"choice_{index}")
        if self.fixed_choices is not None:
            self.solver.add(choice == self.fixed_choices[index])
        branches, enabled = [], []
        self._cache_enabled = True
        self._expr_cache = {}
        not_terminal = z.And(*[old["state"] != m["states"].index(s) for s in m["scope"]["terminal_states"]])
        for j, rule in enumerate(m["transitions"]):
            name = rule["event"]
            origin = m["events"][name]["origin"]
            guard_frame = {**old, "now": new["now"]} if m["semantics"] == CLOCK_SEMANTICS else old
            self._cache_enabled = True
            self._cache_event_name = name
            conditions = [not_terminal, old["state"] == m["states"].index(rule["from"]),
                          new["now"] >= old["now"], self.expr(rule["guard"], guard_frame, fields[name])]
            self._cache_enabled = False
            expiring = None
            if origin == "timer":
                matches = [n for n, spec in m["timers"].items() if spec["event"] == name]
                require(len(matches) == 1, "Symbolic timer event must map to exactly one timer")
                expiring = matches[0]
                conditions += [old["active"][expiring], new["now"] == old["due"][expiring]]
                for other in m["timers"]:
                    if other != expiring:
                        priority = old["due"][expiring] < old["due"][other] if other < expiring else old["due"][expiring] <= old["due"][other]
                        conditions.append(z.Implies(old["active"][other], priority))
            else:
                conditions += [z.Implies(old["active"][n], new["now"] < old["due"][n]) for n in m["timers"]]
            enabled.append((name, z.And(*conditions)))
            if self.fixed_choices is not None and self.fixed_choices[index] != j:
                continue  # exact under the asserted choice; every guard remains encoded
            work = {"state": old["state"], "now": new["now"], "values": dict(old["values"]),
                    "active": dict(old["active"]), "due": dict(old["due"])}
            if expiring:
                work["active"][expiring] = z.BoolVal(False)
            emitted = []
            for action in rule["actions"]:
                kind, arg = next(iter(action.items()))
                if kind == "set":
                    work["values"][arg["var"]] = self.expr(arg["value"], work, fields[name])
                elif kind == "cancel":
                    work["active"][arg] = z.BoolVal(False)
                elif kind == "cancel_if":
                    when = self.expr(arg["when"], work, fields[name])
                    work["active"][arg["timer"]] = z.If(when, z.BoolVal(False), work["active"][arg["timer"]])
                elif kind in ("arm", "arm_if"):
                    when = z.BoolVal(True) if kind == "arm" else self.expr(arg["when"], work, fields[name])
                    delay = self.expr(arg["delay_ms"], work, fields[name])
                    self.action_faults.append(z.And(*conditions, choice == j, when, delay <= 0))
                    work["active"][arg["timer"]] = z.If(when, z.BoolVal(True), work["active"][arg["timer"]])
                    work["due"][arg["timer"]] = z.If(when, new["now"] + delay, work["due"][arg["timer"]])
                elif kind in ("emit", "emit_if"):
                    emitted.append({"message": arg["message"], "fields": {n: self.expr(v, work, fields[name]) for n, v in arg["fields"].items()},
                                    **({"when": self.expr(arg["when"], work, fields[name])} if kind == "emit_if" else {})})
                else:
                    raise ModelError(f"Unsupported symbolic action: {kind}")
            target = z.IntVal(m["states"].index(rule["to"]))
            for case in reversed(rule.get("target_cases", [])):
                target = z.If(self.expr(case["when"], work, fields[name]), m["states"].index(case["to"]), target)
            conditions += [choice == j, new["state"] == target]
            for group in ("values", "active", "due"):
                conditions += [new[group][n] == work[group][n] for n in work[group]]
            branches.append(z.And(*conditions))
            self.branches.append((index, j, emitted))
        self._cache_enabled = False
        self._expr_cache = {}
        # Suffix padding covers every prefix <= depth, including dead-end states.
        unchanged = [new["state"] == old["state"], new["now"] == old["now"]]
        for group in ("values", "active", "due"):
            unchanged += [new[group][n] == old[group][n] for n in old[group]]
        branches.append(z.And(choice == -1, *unchanged))
        if self.clock_progress and self.fixed_choices is None:
            time_only = [choice == -2, new["state"] == old["state"], new["now"] > old["now"]]
            for group in ("values", "active", "due"):
                time_only += [new[group][n] == old[group][n] for n in old[group]]
            time_only += [z.Implies(old["active"][n], new["now"] < old["due"][n]) for n in m["timers"]]
            branches.append(z.And(*time_only))
        self.solver.add(z.Or(*branches))
        if index:
            self.solver.add(z.Implies(z.Int(f"choice_{index-1}") == -1, choice == -1))
        self.conflicts.append(z.Or(*[z.And(a, b) for i, (ea, a) in enumerate(enabled)
                                       for eb, b in enabled[i+1:] if ea == eb]))
        self.enabled.append(enabled)

    def concrete(self, solution, value):
        result = solution.eval(value, model_completion=True)
        if value.sort() == self.z.RealSort():
            require(self.z.is_rational_value(result), "Non-rational symbolic witness is unsupported")
            return {"n": result.numerator_as_long(), "d": result.denominator_as_long()}
        if self.z.is_bool(result):
            return self.z.is_true(result)
        if self.z.is_string_value(result):
            return result.as_string()
        if self.byte_encoding == "sequence" and result.sort() == self.byte_sort:
            # Materialize the already evaluated sequence once. Indexing the
            # original expression repeats nested checksum evaluation per octet.
            # Only concrete Unit/Concat/Empty ASTs use this exact fast path;
            # other model representations retain the generic evaluator below.
            pending = [result];octets = []
            while pending:
                node = pending.pop();kind = node.decl().kind()
                if kind == self.z.Z3_OP_SEQ_EMPTY:
                    continue
                if kind == self.z.Z3_OP_SEQ_UNIT and self.z.is_bv_value(node.arg(0)):
                    octets.append(node.arg(0).as_long())
                elif kind == self.z.Z3_OP_SEQ_CONCAT:
                    pending.extend(reversed(node.children()))
                else:
                    length = solution.eval(self.z.Length(result), model_completion=True).as_long()
                    return [solution.eval(result[i], model_completion=True).as_long() for i in range(length)]
            return octets
        return result.as_long()

    def witness(self, solution):
        m = self.model
        def typed(value, kind):
            if self.byte_encoding == "length" and kind == "bytes":
                return {"byte_length": self.concrete(solution, value)}
            return self.concrete(solution, value)
        initial = {n: typed(v, m["variables"][n]["type"]) for n, v in self.frames[0]["values"].items()}
        steps = []
        for i in range(self.depth):
            choice = self.concrete(solution, self.z.Int(f"choice_{i}"))
            if choice == -1:
                break
            frame = self.frames[i+1]
            if choice == -2:
                steps.append({"at_ms": self.concrete(solution, frame["now"]), "event": None,
                    "origin": "clock", "transition": "@clock_advance", "fields": {},
                    "after": {"state": m["states"][self.concrete(solution, frame["state"])],
                        "variables": {n: typed(v, m["variables"][n]["type"]) for n, v in frame["values"].items()},
                        "timers": {n: self.concrete(solution, frame["due"][n]) for n, active in frame["active"].items() if self.concrete(solution, active)}},
                    "emitted": []})
                continue
            rule = m["transitions"][choice]
            emitted = next(e for index, j, e in self.branches if index == i and j == choice)
            steps.append({"at_ms": self.concrete(solution, frame["now"]), "event": rule["event"],
                          "origin": m["events"][rule["event"]]["origin"], "transition": rule["id"],
                          "fields": {n: typed(v, m["events"][rule["event"]]["fields"][n]) for n, v in self.events[i][rule["event"]].items()},
                          "after": {"state": m["states"][self.concrete(solution, frame["state"])],
                                    "variables": {n: typed(v, m["variables"][n]["type"]) for n, v in frame["values"].items()},
                                    "timers": {n: self.concrete(solution, frame["due"][n]) for n, active in frame["active"].items() if self.concrete(solution, active)}},
                          "emitted": [{"message": e["message"], "fields": {n: typed(v, m["messages"][e["message"]]["fields"][n]) for n, v in e["fields"].items()}} for e in emitted if "when" not in e or self.concrete(solution, e["when"])]})
        return {"initial": initial, "steps": steps}


def check(model, depth=6, symbolic_initials=("iss",), out=None, solver_timeout_ms=10000, solver_preprocess="none"):
    require(type(solver_timeout_ms) is int and 100 <= solver_timeout_ms <= 60000, "Solver budget must be integer 100..60000ms")
    # Validate/prepare journal directory before any solver mutation.
    journal = None
    if out is not None:
        journal = Path(out)
        if journal.exists():
            if not journal.is_dir():
                require(False, "Journal out path exists and is not a directory")
            if any(journal.iterdir()):
                require(False, "Journal out directory must be empty (stale outputs would be reused)")
        else:
            journal.mkdir(parents=True, exist_ok=True)
    enc = Encoding(model, depth, symbolic_initials, solver_preprocess=solver_preprocess)
    enc.solver.set(timeout=solver_timeout_ms)
    z = enc.z
    invariants = [enc.expr(inv["assert"], frame) for frame in enc.frames for inv in model["invariants"]]
    # Save an executable SMT-LIB query, including the exact property being queried.
    enc.solver.push()
    enc.solver.add(z.Or(z.Not(z.And(*invariants)), *enc.action_faults))
    smt = enc.solver.to_smt2()
    # Journal the original safety SMT before the first solve so an interruption
    # leaves the exact query on disk (no result.json until completion).
    if journal is not None:
        (journal / "model.smt2").write_text(smt)
    answer = enc.solve()
    report = {"backend": "z3-bmc", "solver_version": z.get_version_string(), "depth": depth,
              "model_semantic_sha256": model_hash(model), "symbolic_initials": list(symbolic_initials), "solver_timeout_ms": solver_timeout_ms,
              "solver_preprocess": solver_preprocess, "solver_tactics": list(enc.solver_tactics), "solver_preprocess_source": enc.solver_preprocess_source,
              "sequence_width": 32, "event_fields": "all_typed_values", "time": "unbounded_integer_ms",
              "scope": "defined_transitions_and_clock_progress" if enc.clock_progress else "defined_transitions_only",
              "clock_progress": "monotonic_integer_before_next_due" if enc.clock_progress else "not_applicable", "liveness": "not_checked", "unbounded_proof": False,
              "invariants": [i["id"] for i in model["invariants"]], "safety_query": str(answer)}
    report["runtime_properties"] = ["positive_timer_duration"]
    if model["ir_version"] in ("0.2", "0.3", "0.4", "0.5", "0.6"):
        report["byte_semantics"] = "finite_sequence_bv8_truncating_slice"
        report["sequence_order"] = "strict_half_space_partial_order"
    if answer == z.sat:
        report["counterexample"] = enc.witness(enc.solver.model())
        report["replay"] = replay(model, report["counterexample"])
        report["status"] = "counterexample"
    elif answer == z.unsat:
        report["status"] = "bounded_pass"
    else:
        report.update(status="unknown", reason=enc.reason_unknown())
    enc.solver.pop()
    enc.solver.push()
    enc.solver.add(z.Or(*enc.conflicts))
    overlap_smt = enc.solver.to_smt2()
    # Journal the original overlap SMT before the overlap solve.
    if journal is not None:
        (journal / "overlap.smt2").write_text(overlap_smt)
    conflict = enc.solve()
    report["overlap_query"] = str(conflict)
    if conflict == z.sat:
        report["status"] = "conflict"
    elif conflict == z.unknown and report["status"] == "bounded_pass":
        report.update(status="unknown", reason=enc.reason_unknown())
    enc.solver.pop()
    sample_queries={}
    # A satisfying path is cross-checked against independent runtime semantics.
    if report["status"] == "bounded_pass":
        # Nonvacuity is existential. For IR0.4/0.5/0.6 first seek an actual one-event
        # witness with an idle suffix. These SAT subsets never constrain the
        # all-input safety/overlap queries above. Fall back to the original
        # unrestricted witness query if the subsets do not produce a witness.
        strategies=['any-path']
        if model['ir_version']in ('0.4','0.5','0.6')and model['transitions']:
            strategies=['first-rule-one-event','any-rule-one-event',*strategies]
        attempts=[]
        for strategy in strategies:
            sample_enc=Encoding(model,1,symbolic_initials,fixed_choices=[0],solver_preprocess=solver_preprocess)if strategy=='first-rule-one-event'else Encoding(model,1,symbolic_initials,solver_preprocess=solver_preprocess)if strategy=='any-rule-one-event'else enc
            sample_enc.solver.set(timeout=solver_timeout_ms)
            sample_enc.solver.push();sample_enc.solver.add(z.Int('choice_0')>=0)
            sample_smt=sample_enc.solver.to_smt2()
            if journal is not None:
                (journal/("sample-"+strategy+".smt2")).write_text(sample_smt)
            answer=sample_enc.solve()
            record=dict(strategy=strategy,depth=sample_enc.depth,scope='existential_nonvacuity_only',query=str(answer),file='sample-'+strategy+'.smt2',smt2_sha256=hashlib.sha256(sample_smt.encode()).hexdigest())
            if answer==z.unknown:record['reason']=sample_enc.reason_unknown()
            attempts.append(record);sample_queries['sample-'+strategy+'.smt2']=sample_smt
            witness=sample_enc.witness(sample_enc.solver.model())if answer==z.sat else None
            sample_enc.solver.pop()
            if answer==z.sat:break
        report['sample_queries']=attempts
        if answer == z.sat:
            report["sample_witness"] = witness
            report["replay"] = replay(model, report["sample_witness"])
            if report["replay"]["status"] != "match":
                report["status"] = "semantic_mismatch"
        else:
            report["status"] = "unknown" if answer == z.unknown else "vacuous"
            if answer == z.unknown:
                report["reason"] = attempts[-1]['reason']
    if journal is not None:
        for name,query in sample_queries.items():(journal/name).write_text(query)
        report["smt2_sha256"] = hashlib.sha256(smt.encode()).hexdigest()
        report["overlap_smt2_sha256"] = hashlib.sha256(overlap_smt.encode()).hexdigest()
        (journal / "result.json").write_text(json.dumps(report, indent=2) + "\n")
    return report
