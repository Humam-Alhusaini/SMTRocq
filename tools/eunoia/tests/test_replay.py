"""The fixture decoder fails closed; rule computations stay in Rocq."""
import importlib.util
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'tools/eunoia'))
from replay_fixtures import decode, generate
from compile import SignatureError


class ReplayTests(unittest.TestCase):
    def decode_text(self, source):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'proof.cpc'
            path.write_text(source)
            return decode(path)

    def test_every_actual_step_is_decoded(self):
        expected = dict(uf1=25, uf2=9, uf3=14, uf4=15, uf5=22, uf6=10, uf7=3)
        for name, count in expected.items():
            with self.subTest(name=name):
                data = decode(ROOT / 'tools/eunoia/tests/fixtures' / (name + '.cpc'))
                self.assertEqual(len(data[2]), count)

    def test_no_unsupported_command_is_skipped(self):
        with self.assertRaisesRegex(SignatureError, 'unsupported fixture command'):
            self.decode_text('unsat ((assume @p1 true) (assume-push @p2 false))')

    def test_duplicate_id_rejects(self):
        with self.assertRaisesRegex(SignatureError, 'duplicate proof ID'):
            self.decode_text('unsat ((assume @p1 true) (step @p1 :rule refl :args (true)))')

    def test_missing_forward_premise_rejects(self):
        with self.assertRaisesRegex(SignatureError, 'missing/forward premise'):
            self.decode_text('unsat ((step @p1 :rule symm :premises (@p2)))')

    def test_unknown_rule_remains_in_data_for_runtime_rejection(self):
        data = self.decode_text('unsat ((assume @p1 true) (step @p2 :rule novel :premises (@p1)))')
        self.assertEqual(len(data[2]), 1)
        self.assertIn('step_rule := "novel"', data[2][0])

    def test_satisfiable_marker_is_not_accepted(self):
        with self.assertRaisesRegex(SignatureError, 'expected unsat'):
            self.decode_text('sat ()')

    def test_replay_generation_is_deterministic(self):
        paths = sorted((ROOT / 'tools/eunoia/tests/fixtures').glob('*.cpc'))
        self.assertEqual(generate(paths), generate(paths))
