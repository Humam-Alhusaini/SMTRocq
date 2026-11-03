#!/usr/bin/env python3
"""Adversarial syntax/capture tests; these establish no CPC proof soundness."""

import contextlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import dump_cpc
from cpc_inventory import expressions, input_logic, inventory, signature_rules
from verify_toolchain import MANIFEST, file_sha256, verify_toolchain


RULES = {name: {"contains_sorry": False} for name in ("cong", "scope")}
RULES["trust"] = {"contains_sorry": True}
PROOF = "unsat\n((assume @p1 (= x y)) (step @p2 false :rule cong :premises (@p1)))"


class InventoryTests(unittest.TestCase):
    def test_comments_and_quoted_rule_text_are_opaque(self):
        proof = PROOF.replace("x y", '|x :rule trust| |y ( ) ;|')
        proof = proof.replace("(assume", '; :rule trust\n(assume')
        self.assertEqual(inventory(proof, RULES)["rules"], {"cong": 1})
        self.assertEqual(expressions('(a "a"";()b")'), [["a", '"a"";()b"']])

    def test_malformed_and_incomplete_dumps_are_rejected(self):
        corruptions = [
            PROOF[:-1], PROOF + ")", PROOF + " unsat", "sat", "unknown",
            "unsat ()", PROOF.replace("false", "true"),
            PROOF.replace(":rule cong", ":rule unknown_rule"),
            PROOF.replace(":rule cong", ":rule trust"),
            PROOF.replace(":rule cong", ":premises ()"),
            PROOF.replace(":rule cong", ":rule cong :rule cong"),
            PROOF.replace("(step", "(step-pop"),
            PROOF.replace("(assume", "(assume-push"),
            PROOF.replace("(assume", "(unrecognized"),
            'unsat (((a)) (step @p false :rule cong))',
            'unsat ((define x () "unterminated))',
        ]
        for proof in corruptions:
            with self.subTest(proof=proof), self.assertRaises(ValueError):
                inventory(proof, RULES)

    def test_scope_pop_is_inventoried_as_a_step(self):
        proof = ('unsat ((assume-push @a true) (step @b false :rule cong) '
                 '(step-pop @c :rule scope :premises (@b)) '
                 '(step @d false :rule cong :premises (@c)))')
        result = inventory(proof, RULES)
        self.assertEqual(result["rules"], {"cong": 2, "scope": 1})
        self.assertEqual(result["steps"], 3)

    def test_input_queries_options_and_logics(self):
        self.assertEqual(input_logic('(set-logic QF_LIA) (assert false) (check-sat)'), "QF_LIA")
        for text in (
                '(set-logic ALL) (check-sat)',
                '(set-logic QF_UF) (check-sat) (check-sat)',
                '(set-logic QF_UF) (check-sat) (get-proof)',
                '(set-logic QF_UF) (set-option :proof-allow-trust true) (check-sat)',
                '(set-logic QF_UF) (exit) (check-sat)',
                '((a)) (set-logic QF_UF) (check-sat)'):
            with self.subTest(text=text), self.assertRaises(ValueError):
                input_logic(text)

    def test_rules_come_from_signature_includes(self):
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            signature = base / "Cpc.eo"
            signature.write_text('(include "./rules.eo")')
            (base / "rules.eo").write_text(
                '(declare-rule new_rule () :conclusion false) '
                '(declare-rule hole () :conclusion false :sorry)')
            rules = signature_rules(signature)
            self.assertEqual(inventory(PROOF.replace("cong", "new_rule"), rules)["steps"], 1)
            with self.assertRaisesRegex(ValueError, "incomplete"):
                inventory(PROOF.replace("cong", "hole"), rules)
            signature.write_text('(include "../outside.eo")')
            with self.assertRaisesRegex(ValueError, "escapes"):
                signature_rules(signature)


class CaptureTests(unittest.TestCase):
    def test_failed_runs_never_publish_partial_results(self):
        # Simulated process failures/output are not substitute solver evidence.
        for mode in ("sat", "empty", "nonzero", "timeout", "oserror", "oversize", "trust"):
            def execute(command, **kwargs):
                if "stdout" not in kwargs:
                    return subprocess.CompletedProcess(command, 0, "source-revision\n")
                if mode == "timeout":
                    raise subprocess.TimeoutExpired(command, 1)
                if mode == "oserror":
                    raise OSError("cannot execute")
                data = {"sat": "sat\n", "empty": "", "trust": PROOF.replace("cong", "trust")}
                kwargs["stdout"].write(data.get(mode, PROOF).encode())
                return subprocess.CompletedProcess(command, 9 if mode == "nonzero" else 0)

            with tempfile.TemporaryDirectory() as directory:
                output = Path(directory) / "results"
                argv = ["dump_cpc.py", "--output", str(output), "--profile", "default"]
                if mode == "oversize":
                    argv += ["--max-dump-bytes", "1"]
                with patch.object(sys, "argv", argv), \
                        patch.object(dump_cpc, "verify_toolchain", return_value={
                            "binary": "unused", "signature": "unused"}), \
                        patch.object(dump_cpc, "signature_rules", return_value=RULES), \
                        patch.object(dump_cpc.subprocess, "run", side_effect=execute), \
                        contextlib.redirect_stderr(io.StringIO()):
                    self.assertEqual(dump_cpc.main(), 1, mode)
                self.assertFalse(output.exists())
                self.assertEqual(list(Path(directory).iterdir()), [])

    def test_existing_output_is_preserved(self):
        with tempfile.TemporaryDirectory() as directory:
            sentinel = Path(directory) / "sentinel"
            sentinel.write_text("keep me")
            with patch.object(sys, "argv", ["dump_cpc.py", "--output", directory]), \
                    contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(dump_cpc.main(), 1)
            self.assertEqual(sentinel.read_text(), "keep me")


class ToolchainTests(unittest.TestCase):
    def test_global_and_relative_roots_are_rejected(self):
        for root in ("/usr", "/usr/local", "/", "."):
            with self.subTest(root=root), self.assertRaises(ValueError):
                verify_toolchain(root)

    def test_corrupt_archive_fails_before_solver_execution(self):
        with tempfile.TemporaryDirectory() as directory:
            downloads = Path(directory) / "downloads"
            downloads.mkdir()
            name = json.loads(MANIFEST.read_text())["archives"]["binary"]["filename"]
            (downloads / name).write_bytes(b"invalid archive, never an installed dependency")
            with patch("verify_toolchain.subprocess.run") as execute:
                with self.assertRaisesRegex(ValueError, "checksum mismatch"):
                    verify_toolchain(directory)
                execute.assert_not_called()


class FixtureTests(unittest.TestCase):
    def test_retained_bytes_inputs_and_step_counts_match_provenance(self):
        base = dump_cpc.REPOSITORY / "unit-tests/eunoia-fixtures"
        selection = json.loads((base / "fixtures.json").read_text())
        report_path = base / selection["capture_inventory"]
        self.assertEqual(file_sha256(report_path), selection["capture_inventory_sha256"])
        report = json.loads(report_path.read_text())
        self.assertEqual(report["status"], "UNVERIFIED_SOLVER_OUTPUT")
        rows = {row["proof"]: row for row in report["runs"]}
        for name in selection["fixtures"]:
            row = rows[name]
            proof = base / name
            with self.subTest(fixture=name):
                self.assertEqual(file_sha256(proof), row["proof_sha256"])
                self.assertEqual(proof.stat().st_size, row["proof_bytes"])
                self.assertEqual(file_sha256(dump_cpc.REPOSITORY / row["input"]), row["input_sha256"])
                counts = inventory(proof.read_text(), report["rule_declarations"])
                for field in ("commands", "rules", "steps"):
                    self.assertEqual(counts[field], row[field])
                self.assertEqual(counts["steps"], counts["commands"].get("step", 0) +
                                 counts["commands"].get("step-pop", 0))


if __name__ == "__main__":
    unittest.main(verbosity=2)
