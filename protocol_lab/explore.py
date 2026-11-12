"""Bounded exploration using the reference semantics, not an independent proof."""
import copy

from .ir import Conflict, Machine, ModelError, Uncovered, evaluate, infer, require


def explore(model, config):
    depth = config["depth"]
    require(type(depth) is int and 1 <= depth <= 20, "Exploration depth must be 1..20")
    for case in config["cases"]:
        require(all(s in model["states"] for s in case["states"]), "Unknown exploration state")
        schema = model["events"].get(case["event"], {})
        require(schema.get("origin") in ("application", "network"), "Bad exploration event")
        require(set(case["fields"]) == set(schema["fields"]), "Exploration fields mismatch")
        for key, expr in case["fields"].items():
            require(infer(expr, model) == schema["fields"][key], "Exploration expression type mismatch")
    report = {"status": "bounded_pass", "backend": "reference-explicit-explorer",
              "independent_formal_proof": False, "depth": depth,
              "initials": config["initials"], "event_domains": config["cases"],
              "visited_prefixes": 0, "edges": 0, "covered_transitions": [],
              "uncovered": [], "conflicts": [], "counterexamples": [], "cutoff_prefixes": 0,
              "liveness": "not_checked", "completeness": "not_claimed"}
    covered, gaps = set(), set()
    stack = []
    for initial in config["initials"]:
        try:
            stack.append((Machine(model, initial), [], initial))
        except ModelError as exc:
            report["counterexamples"].append({"initial": initial, "steps": [], "error": str(exc)})
    while stack:
        machine, path, initial = stack.pop()
        report["visited_prefixes"] += 1
        if machine.state in model["scope"]["terminal_states"]:
            continue
        if len(path) >= depth:
            report["cutoff_prefixes"] += 1
            continue
        choices = [{"at_ms": machine.now_ms, "event": c["event"],
                    "fields": {k: evaluate(v, machine) for k, v in c["fields"].items()}}
                   for c in config["cases"] if machine.state in c["states"]]
        if machine.timers:
            choices.append({"at_ms": min(machine.timers.values()), "tick": True})
        for choice in choices:
            child = copy.deepcopy(machine)
            try:
                if choice.get("tick"):
                    child.tick(choice["at_ms"])
                else:
                    child.dispatch(choice["event"], choice["fields"], choice["at_ms"])
            except Uncovered as exc:
                key = (machine.state, str(choice))
                if key not in gaps:
                    report["uncovered"].append({"initial": initial, "steps": path + [choice], "error": str(exc),
                                                "classification": "model_coverage_gap; not_a_specification_verdict"})
                    gaps.add(key)
                continue
            except Conflict as exc:
                report["conflicts"].append({"initial": initial, "steps": path + [choice], "error": str(exc)})
                continue
            except ModelError as exc:
                report["counterexamples"].append({"initial": initial, "steps": path + [choice], "error": str(exc)})
                continue
            report["edges"] += 1
            covered.update(r["transition"] for r in child.trace[len(machine.trace):])
            stack.append((child, path + [choice], initial))
    report["covered_transitions"] = sorted(covered)
    report["uncovered_transitions"] = sorted({t["id"] for t in model["transitions"]} - covered)
    if report["conflicts"] or report["counterexamples"]:
        report["status"] = "fail"
    return report
