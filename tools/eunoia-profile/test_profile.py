import importlib.util
import json
from pathlib import Path
import tempfile
import unittest


def load(name):
    spec = importlib.util.spec_from_file_location(name, Path(__file__).with_name(name + ".py"))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


run = load("run")
instrument = load("instrument")


class ProfileTests(unittest.TestCase):
    def summarize(self, events):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "trace.json"
            path.write_text(json.dumps({"traceEvents": events}))
            return run.trace_summary(path)

    def test_nested_times_are_not_added_twice(self):
        events = [{"name": name, "ph": phase, "ts": ts}
                  for name, phase, ts in [("outer", "B", 0), ("child", "B", 10),
                                          ("child", "E", 30), ("outer", "E", 100)]]
        summary = self.summarize(events)
        self.assertEqual(summary["outer"]["calls"], 1)
        self.assertAlmostEqual(summary["outer"]["inclusive_s"], .0001)
        self.assertAlmostEqual(summary["outer"]["visible_self_s"], .00008)

    def test_repeated_calls_are_counted(self):
        events = [{"name": "a", "ph": phase, "ts": ts}
                  for phase, ts in [("B", 0), ("E", 10), ("B", 20), ("E", 40)]]
        self.assertEqual(self.summarize(events)["a"]["calls"], 2)

    def test_incomplete_trace_rejected(self):
        with self.assertRaises(ValueError):
            self.summarize([{"name": "a", "ph": "B", "ts": 0}])

    def test_mismatched_trace_rejected(self):
        with self.assertRaises(ValueError):
            self.summarize([{"name": "a", "ph": "B", "ts": 0},
                            {"name": "b", "ph": "E", "ts": 1}])

    def test_instrumentation_retains_checks(self):
        source = instrument.SOURCE.read_text()
        modified = instrument.instrument(source)
        self.assertEqual(modified.count("R.cbv_vm env"), 1)  # forwarding helper
        self.assertEqual(modified.count("profile_vm env"), 3)
        self.assertIn("R.vm_conv Conversion.CUMUL env computation", modified)
        self.assertIn("on_failure ();", modified)
        self.assertIn("R.mkCast", modified)
        with self.assertRaises(ValueError):
            instrument.instrument(modified)

    def test_changed_anchor_rejected(self):
        with self.assertRaises(ValueError):
            instrument.instrument("let global = ()")


if __name__ == "__main__":
    unittest.main()
