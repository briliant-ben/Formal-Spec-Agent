"""Protocol-neutral fixed-input reference contracts; network adapters stay with benchmarks."""
import copy
from .ir import Machine, ModelError, require, value_ok

class TraceContractMismatch(ModelError):
    """A reference execution violates an independent fixed-input output contract."""
    def __init__(self, scenario, at_ms, expected, observed):
        super().__init__(f"Scenario trace contract mismatch: {scenario} at {at_ms}ms")
        self.scenario = scenario
        self.at_ms = at_ms
        self.expected = copy.deepcopy(expected)
        self.observed = copy.deepcopy(observed)

def run_scenario(model, scenario, *, snapshots=None):
    require(scenario.get("scenario_version") in ("0.1", "0.2"), "Unsupported scenario version")
    machine = Machine(model, scenario.get("initial"))
    if snapshots is not None:
        require(type(snapshots) is list and not snapshots, "Snapshot capture target must be empty list")
        snapshots.append(copy.deepcopy(machine.snapshot()))
    for step in scenario["steps"]:
        if "expect_trace" in step:
            require(scenario["scenario_version"] == "0.2", "Trace contracts require scenario 0.2")
            contract = step["expect_trace"]
            require(type(contract) is list, "Bad trace contract list")
            for row in contract:
                require(type(row) is dict and set(row) == {"at_ms", "emitted"}, "Bad trace contract row")
                require(type(row["at_ms"]) is int and row["at_ms"] >= 0, "Bad trace contract time")
                require(type(row["emitted"]) is list, "Bad trace contract emissions")
                for output in row["emitted"]:
                    require(type(output) is dict and set(output) == {"message", "fields"}, "Bad trace contract output")
                    require(type(output["message"]) is str, "Bad trace contract message")
                    schema = model["messages"].get(output["message"])
                    require(schema is not None and type(output["fields"]) is dict
                            and set(output["fields"]) == set(schema["fields"]), "Bad trace contract message fields")
                    require(all(value_ok(output["fields"][key], kind) for key, kind in schema["fields"].items()), "Bad trace contract field type")
        trace_start = len(machine.trace)
        if step.get("tick"):
            machine.tick(step["at_ms"])
        else:
            machine.dispatch(step["event"], step.get("fields", {}), step["at_ms"])
        if snapshots is not None:
            snapshots.append(copy.deepcopy(machine.snapshot()))
        if "expect_trace" in step:
            observed = [{"at_ms": row["time_ms"], "emitted": row["emitted"]} for row in machine.trace[trace_start:]]
            if observed != step["expect_trace"]:
                raise TraceContractMismatch(scenario["id"], step["at_ms"], step["expect_trace"], observed)
    if "settle_ms" in scenario:
        machine.tick(scenario["settle_ms"])
        if snapshots is not None:
            snapshots.append(copy.deepcopy(machine.snapshot()))
    expected = scenario["expect"]
    require(machine.state == expected["state"], "Scenario final state mismatch")
    for key, value in expected.get("variables", {}).items():
        require(machine.values.get(key) == value, f"Scenario variable mismatch: {key}")
    require(machine.timers == expected["timers"], "Scenario timer mismatch")
    return machine
