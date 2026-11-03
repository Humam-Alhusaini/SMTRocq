"""Regression checks for solved-count integrity and the timeout boundary."""

from pathlib import Path
import signal
import sys
import tempfile
import time
import unittest

import run


class BenchmarkIntegrity(unittest.TestCase):
    def setUp(self):
        self.positive = {"expected": "proved"}
        self.negative = {"expected": "rejected"}
        self.success = {"exit_code": 0, "timeout": False}
        self.failure = {"exit_code": 1, "timeout": False}
        self.output = (f"{run.BEGIN}\n"
                       "Finished transaction in 0.123 secs (0.08u,0.s) (successful)\n"
                       "Finished transaction in 0.002 secs (0.002u,0.s) (successful)\n"
                       f"{run.END} {run.ASSUMPTIONS}\nClosed under the global context\n{run.DONE}\n")

    def test_accept_only_completed_proof_with_timings(self):
        row = run.classify(self.positive, self.success, self.output, True)
        self.assertTrue(row["solved"])
        self.assertEqual(row["tactic_wall_s"], 0.123)
        self.assertEqual(row["qed_wall_s"], 0.002)
        for output, vo in ((self.output, False), (self.output.replace(run.DONE, ""), True),
                           (self.output.replace("0.123 secs", "unparseable"), True)):
            self.assertFalse(run.classify(self.positive, self.success, output, vo)["solved"])

    def test_qed_failure_is_unsolved(self):
        self.assertFalse(run.classify(self.positive, self.failure, self.output, True)["solved"])

    def test_negative_success_is_a_failure_never_solved(self):
        row = run.classify(self.negative, self.success, self.output, True)
        self.assertFalse(row["solved"])
        self.assertEqual(row["status"], "negative_unexpected_success")

    def test_negative_import_error_is_not_an_expected_rejection(self):
        row = run.classify(self.negative, self.failure, "Error: missing library", False)
        self.assertEqual(row["status"], "error")
        rejected = run.classify(self.negative, self.failure, run.BEGIN + "\nError: sat", False)
        self.assertEqual(rejected["status"], "negative_rejected")

    def test_timeout_never_passes_a_negative(self):
        row = run.classify(self.negative, {"exit_code": -9, "timeout": True}, run.BEGIN, False)
        self.assertEqual(row["status"], "timeout")
        self.assertFalse(row["solved"])

    def test_unavailable_and_negative_rows_do_not_inflate_solved_counts(self):
        base = {"backend": "cvc4", "theory": "UF", "process_wall_s": 1,
                "tactic_wall_s": 0.2, "qed_wall_s": 0.01}
        rows = [base | {"case_id": "good", "expected": "proved", "status": "solved", "solved": True},
                base | {"case_id": "good", "expected": "proved", "status": "error", "solved": False},
                base | {"case_id": "negative", "expected": "rejected", "status": "negative_rejected", "solved": False},
                base | {"case_id": "absent", "expected": "proved", "status": "unavailable", "solved": False,
                        "process_wall_s": None}]
        summary = run.summarize(rows)["cvc4"]
        self.assertEqual(summary["positive_cases"], 2)
        self.assertEqual(summary["positive_scheduled"], 3)
        self.assertEqual(summary["positive_attempts"], 2)
        self.assertEqual(summary["solved_attempts"], 1)
        self.assertEqual(summary["cases_solved_every_repeat"], 0)

    def test_timeout_kills_solver_descendants(self):
        with tempfile.TemporaryDirectory(prefix="eunoia-timeout-") as directory:
            marker = Path(directory) / "solver_survived"
            child = f"import time; from pathlib import Path; time.sleep(0.5); Path({str(marker)!r}).touch()"
            parent = f"import subprocess, sys, time; subprocess.Popen([sys.executable, '-c', {child!r}]); time.sleep(30)"
            result = run.execute([sys.executable, "-c", parent], directory, 0.1)
            self.assertTrue(result["timeout"])
            self.assertEqual(result["exit_code"], -signal.SIGKILL)
            time.sleep(0.6)
            self.assertFalse(marker.exists())

    def test_manifest_has_valid_positive_and_negative_cases(self):
        cases = run.load_cases(run.HERE / "cases.json")
        self.assertEqual(len(cases), 14)
        self.assertEqual(sum(c["expected"] == "proved" for c in cases), 12)
        self.assertEqual({c["theory"] for c in cases if c["expected"] == "rejected"}, {"UF", "LIA"})


if __name__ == "__main__":
    unittest.main()
