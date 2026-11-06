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
    def decode_text(self, source, scoped=False):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'proof.cpc'
            path.write_text(source)
            return decode(path, scoped=scoped)

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
        paths = sorted((ROOT / 'tools/eunoia/tests/fixtures').glob('uf*.cpc'))
        self.assertEqual(generate(paths), generate(paths))


    def test_lia_step_and_scope_counts(self):
        counts = [131, 27, 28, 26, 110, 30, 27]
        for i, count in enumerate(counts, 1):
            data = decode(ROOT / f'tools/eunoia/tests/fixtures/lia{i}.cpc', scoped=True)
            self.assertEqual(sum('TraceStep' in c or 'TracePop' in c for c in data[2]), count)
            self.assertEqual(sum('TracePush' in c for c in data[2]), 6 if i in (1, 5) else 0)

    def test_strict_shift_keeps_every_step_and_exact_tightening_arguments(self):
        data = decode(ROOT / 'tools/eunoia/tests/fixtures/lia_strict_shift.cpc', scoped=True)
        self.assertEqual(len(data[1]), 1)
        self.assertEqual(len(data[2]), 32)
        self.assertEqual(data[3], 33)
        step = data[2][18]
        self.assertIn('step_id := 20; step_rule := "arith-geq-tighten"', step)
        self.assertIn('step_args := [(Apply (Apply (Symbol "+") (Symbol "op_1")) '
                      '(Apply (Apply (Symbol "*") (Symbol "-1")) (Symbol "op_0"))); (Symbol "1")]', step)
        self.assertIn('step_premises := []', step)

    def test_scope_ids_are_restored_and_may_be_reused(self):
        source = 'unsat ((assume @p1 true) (assume-push @p2 true) (step @p3 :rule refl :args (true)) (step-pop @p2 :rule scope :premises (@p3)) (step @p3 :rule refl :args (true)))'
        data = self.decode_text(source, scoped=True)
        self.assertEqual(len(data[2]), 4)
        self.assertIn('TracePop', data[2][2])

    def test_scope_leaks_and_unbalanced_commands_reject(self):
        for source, error in [
            ('unsat ((assume-push @p1 true))', 'unclosed'),
            ('unsat ((step-pop @p1 :rule scope :premises ()))', 'without push'),
            ('unsat ((assume-push @p1 true) (step @p2 :rule refl :args (true)) (step-pop @p3 :rule scope :premises (@p2)) (step @p4 :rule symm :premises (@p2)))', 'missing/forward'),
        ]:
            with self.subTest(source=source), self.assertRaisesRegex(SignatureError, error):
                self.decode_text(source, scoped=True)

    def test_scoped_generation_is_deterministic(self):
        paths = sorted((ROOT / 'tools/eunoia/tests/fixtures').glob('lia*.cpc'))
        self.assertEqual(generate(paths, scoped=True), generate(paths, scoped=True))

    def test_integer_captures_retain_casts_coefficients_and_nested_scopes(self):
        fixtures = ROOT / 'tools/eunoia/tests/integer-fixtures'
        expected = {'lia_parity': (1, 8, 0, 0), 'lia_coefficient_bound': (2, 16, 0, 0),
                    'lia_coefficient_scoped': (1, 140, 6, 3)}
        for name, (roots, steps, pushes, max_depth) in expected.items():
            data = decode(fixtures / (name + '.cpc'), scoped=True)
            self.assertEqual(len(data[1]), roots)
            self.assertEqual(sum('TraceStep' in c or 'TracePop' in c for c in data[2]), steps)
            self.assertEqual(sum('TracePush' in c for c in data[2]), pushes)
            depth = maximum = 0
            for c in data[2]:
                depth += int('TracePush' in c) - int('TracePop' in c)
                maximum = max(maximum, depth)
            self.assertEqual((depth, maximum), (0, max_depth))
            self.assertIn('Symbol "to_real"', ''.join(data[2]))
            self.assertIn('Symbol "to_int"', ''.join(data[2]))
        self.assertIn('Symbol "-3/2"', ''.join(decode(fixtures / 'lia_coefficient_bound.cpc', scoped=True)[2]))
        paths = sorted(fixtures.glob('*.cpc'))
        self.assertEqual(generate(paths, scoped=True), generate(paths, scoped=True))
