"""Logical timer transitions, independent of public batched tick operations."""
import copy
import unittest

from protocol_lab.ir import Machine, ModelError
from protocol_lab.symbolic import crosscheck_trace, replay


def timer_model():
    increment = {"op": "add", "args": [{"var": "x"}, 1]}
    return {
        "ir_version": "0.2", "semantics": "flat-efsm-atomic-ordered-v1",
        "protocol": "logical-timer-replay", "scope": {"terminal_states": []},
        "states": ["S"], "initial_state": "S",
        "requirements": {"R": {"source": "docs/semantics.md",
                                  "interpretation": "Ordered scheduled transitions"}},
        "variables": {"x": {"type": "int", "initial": 0}},
        "events": {"start": {"origin": "application", "fields": {}},
                   "go": {"origin": "application", "fields": {}},
                   "timer.a": {"origin": "timer", "fields": {}},
                   "timer.b": {"origin": "timer", "fields": {}}},
        "timers": {"a": {"event": "timer.a"}, "b": {"event": "timer.b"}},
        "messages": {"mark": {"fields": {"value": "int"}}},
        "transitions": [
            {"id": "START", "from": "S", "to": "S", "event": "start",
             "guard": True, "actions": [
                 {"arm": {"timer": "b", "delay_ms": 10}},
                 {"arm": {"timer": "a", "delay_ms": 10}}], "requirements": ["R"]},
            {"id": "TA", "from": "S", "to": "S", "event": "timer.a",
             "guard": True, "actions": [{"set": {"var": "x", "value": increment}},
                 {"emit": {"message": "mark", "fields": {"value": 1}}}], "requirements": ["R"]},
            {"id": "TB", "from": "S", "to": "S", "event": "timer.b",
             "guard": True, "actions": [{"set": {"var": "x", "value": increment}},
                 {"emit": {"message": "mark", "fields": {"value": 2}}}], "requirements": ["R"]},
            {"id": "GO", "from": "S", "to": "S", "event": "go", "guard": True,
             "actions": [{"set": {"var": "x", "value": 99}}], "requirements": ["R"]}],
        "invariants": [{"id": "nonnegative", "requirements": ["R"],
                        "assert": {"op": "ge", "args": [{"var": "x"}, 0]}}]}


class SymbolicTimerReplayTests(unittest.TestCase):
    def test_tied_timers_and_prefix_match_each_logical_transition(self):
        model = timer_model()
        machine = Machine(model)
        machine.dispatch("start", {}, 0)
        machine.tick(10)
        self.assertEqual([r["transition"] for r in machine.trace], ["START", "TA", "TB"])
        checked = crosscheck_trace(model, machine.trace)
        self.assertEqual((checked["query"], checked["status"]), ("sat", "match"))
        prefix = copy.deepcopy(checked["witness"])
        prefix["steps"] = prefix["steps"][:2]
        self.assertEqual(prefix["steps"][-1]["after"]["timers"], {"b": 10})
        self.assertEqual(replay(model, prefix), {"status": "match", "compared_steps": 2})

    def test_one_step_and_batched_tick_have_identical_records(self):
        model = timer_model()
        stepped, batched = Machine(model), Machine(model)
        for machine in (stepped, batched):
            machine.dispatch("start", {}, 0)
        stepped.step_timer(10)
        self.assertEqual((stepped.values["x"], stepped.timers), (1, {"b": 10}))
        stepped.step_timer(10)
        batched.tick(10)
        self.assertEqual(stepped.trace, batched.trace)
        self.assertEqual(stepped.snapshot(), batched.snapshot())

    def test_cancellation_and_rearm_are_not_overridden_by_witness(self):
        for action in ({"cancel": "b"}, {"arm": {"timer": "b", "delay_ms": 5}}):
            with self.subTest(action=action):
                model = timer_model()
                model["transitions"][1]["actions"].append(action)
                machine = Machine(model)
                machine.dispatch("start", {}, 0)
                machine.tick(15)
                result = crosscheck_trace(model, machine.trace)
                self.assertEqual((result["query"], result["status"]), ("sat", "match"))
                if "arm" in action:
                    self.assertEqual(machine.trace[-1]["time_ms"], 15)
                    forged = copy.deepcopy(result["witness"])
                    forged["steps"][-1]["at_ms"] = 10
                    self.assertEqual(replay(model, forged)["status"], "runtime_rejected")
                else:
                    self.assertEqual([r["transition"] for r in machine.trace], ["START", "TA"])

    def test_wrong_timer_labels_do_not_match_unchanged_after_or_emissions(self):
        model = timer_model()
        model["transitions"][0]["actions"] = [{"arm": {"timer": "a", "delay_ms": 10}}]
        machine = Machine(model)
        machine.dispatch("start", {}, 0)
        machine.tick(10)
        witness = crosscheck_trace(model, machine.trace)["witness"]
        for edits in ({"event": "timer.b"}, {"transition": "TB"}, {"origin": "network"}):
            with self.subTest(edits=edits):
                forged = copy.deepcopy(witness)
                forged["steps"][-1].update(edits)
                self.assertNotEqual(replay(model, forged)["status"], "match")

    def test_external_step_cannot_hide_earlier_timers(self):
        model = timer_model()
        machine = Machine(model)
        machine.dispatch("start", {}, 0)
        machine.dispatch("go", {}, 10)
        result = crosscheck_trace(model, machine.trace)
        self.assertEqual(result["status"], "match")
        forged = copy.deepcopy(result["witness"])
        forged["steps"] = [forged["steps"][0], forged["steps"][-1]]
        self.assertEqual(replay(model, forged)["status"], "semantic_mismatch")

    def test_bad_step_is_atomic_and_timer_injection_stays_forbidden(self):
        machine = Machine(timer_model())
        with self.assertRaisesRegex(ModelError, "No active timer"):
            machine.step_timer(0)
        machine.dispatch("start", {}, 0)
        for time_ms in (9, 11, -1, True):
            before = copy.deepcopy((machine.snapshot(), machine.now_ms, machine.trace))
            with self.assertRaises(ModelError):
                machine.step_timer(time_ms)
            self.assertEqual((machine.snapshot(), machine.now_ms, machine.trace), before)
        with self.assertRaisesRegex(ModelError, "cannot be injected"):
            machine.dispatch("timer.a", {}, 10)

        invalid = timer_model()
        invalid["transitions"][1]["actions"][0] = {"set": {"var": "x", "value": -1}}
        machine = Machine(invalid)
        machine.dispatch("start", {}, 0)
        before = copy.deepcopy((machine.snapshot(), machine.now_ms, machine.trace))
        with self.assertRaisesRegex(ModelError, "Invariant failed"):
            machine.step_timer(10)
        self.assertEqual((machine.snapshot(), machine.now_ms, machine.trace), before)

    def test_malformed_and_wrong_semantics_clock_witness_is_rejected(self):
        model = timer_model()
        self.assertEqual(replay(model, {"initial": {"x": 0}, "steps": [{}]})["status"], "runtime_rejected")
        step = {"at_ms": 1, "event": None, "origin": "clock", "transition": "@clock_advance",
                "fields": {}, "after": Machine(model).snapshot(), "emitted": []}
        self.assertEqual(replay(model, {"initial": {"x": 0}, "steps": [step]})["status"], "runtime_rejected")


if __name__ == "__main__":
    unittest.main()
