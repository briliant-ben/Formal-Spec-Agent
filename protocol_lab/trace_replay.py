"""Strict reference replay of explicit external, timer and clock trace steps."""
from .ir import CLOCK_SEMANTICS, Machine, ModelError, require


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
