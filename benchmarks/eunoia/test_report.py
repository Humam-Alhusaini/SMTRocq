"""Report integrity: coverage differences must not produce misleading timings."""
import unittest

import report


def row(backend, case, repeat=1, status='solved', expected='proved'):
    return dict(backend=backend, case_id=case, repeat=repeat, theory='UF',
                status=status, expected=expected, solved=status == 'solved',
                tactic_wall_s=0.5, qed_wall_s=0.1)


class ReportIntegrity(unittest.TestCase):
    def test_compare_only_shared_checked_attempts(self):
        rows = [row('a', 'one'), row('b', 'one'), row('a', 'two'),
                row('b', 'two', status='error'), row('a', 'one', repeat=2)]
        coverage, paired = report.tables(rows)
        self.assertEqual(coverage[0][1:3], (3, 3))
        self.assertEqual(coverage[1][1:3], (1, 2))
        self.assertEqual(paired, [('a', 'b', 1, 0.5, 0.5, 0.1, 0.1)])

    def test_negative_and_unavailable_attempts_have_no_latency(self):
        rows = [row('a', 'one'), row('b', 'one', status='unavailable'),
                row('a', 'false', status='negative_rejected', expected='rejected')]
        coverage, paired = report.tables(rows)
        self.assertEqual(coverage[0][1:5], (1, 1, 1, 1))
        self.assertEqual(paired[0][2:], (0, 0, 0, 0, 0))
        self.assertIn('unmeasured', report.markdown(rows))

    def test_duplicate_or_invalid_checked_rows_reject(self):
        good = row('a', 'one')
        with self.assertRaisesRegex(ValueError, 'Duplicate'):
            report.tables([good, good])
        for altered in [good | dict(expected='rejected'),
                        good | dict(tactic_wall_s=float('nan')),
                        good | dict(qed_wall_s=-1)]:
            with self.assertRaises(ValueError):
                report.tables([altered])


if __name__ == '__main__':
    unittest.main()
