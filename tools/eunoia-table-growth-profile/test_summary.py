"""Exercise dependency accounting independently of native proof search."""
import json
from pathlib import Path
import importlib.util
import unittest

spec = importlib.util.spec_from_file_location('table_summary', Path(__file__).with_name('summarize.py'))
summary = importlib.util.module_from_spec(spec)
spec.loader.exec_module(summary)


def event(i, phase, atoms, forms, **kw):
    return 'EUNOIA_TABLE ' + json.dumps(dict(id=i, event=phase, atoms=atoms, forms=forms, **kw))


class SummaryTests(unittest.TestCase):
    def test_later_source_reuses_auxiliary(self):
        log = '\n'.join([
            event(1, 'begin', 2, 3, source_atoms=[0], source_forms=[2]),
            event(1, 'end', 5, 6, status='ok', retained_atoms=[0, 2], retained_forms=[2, 3]),
            # Atom 3/form 4 become source dependencies later, despite no new
            # interning. Atom 4/form 5 remain discarded native search work.
            event(2, 'begin', 6, 7, source_atoms=[3, 5], source_forms=[4, 6]),
            event(2, 'end', 6, 7, status='ok', retained_atoms=[5], retained_forms=[6]),
        ])
        result = summary.summarize(log)
        self.assertEqual(result['completed_calls'], 2)
        self.assertEqual(result['atoms']['search_created'], 3)
        self.assertEqual(result['atoms']['search_created_source_required'], 1)
        self.assertEqual(result['atoms']['search_created_certificate_only'], 1)
        self.assertEqual(result['atoms']['unused_indices'], [4])
        self.assertEqual(result['forms']['unused_indices'], [5])
        self.assertEqual(result['atoms']['final_observed'], 6)

    def test_failed_search_entries_are_counted(self):
        result = summary.summarize('\n'.join([
            event(1, 'begin', 2, 3, source_atoms=[], source_forms=[]),
            event(1, 'end', 3, 4, status='error', retained_atoms=[], retained_forms=[]),
        ]))
        self.assertEqual(result['atoms']['unused_indices'], [2])
        self.assertEqual(result['forms']['unused_indices'], [3])

    def test_interruption_is_explicit(self):
        result = summary.summarize(event(1, 'begin', 2, 3, source_atoms=[], source_forms=[]))
        self.assertEqual(result['open_calls'], [1])
        self.assertIsNone(result['atoms']['final_observed'])

    def test_reset_is_rejected(self):
        with self.assertRaises(ValueError):
            summary.summarize('\n'.join([
                event(1, 'begin', 2, 3, source_atoms=[], source_forms=[]),
                event(1, 'end', 3, 4, status='ok', retained_atoms=[], retained_forms=[]),
                event(2, 'begin', 2, 3, source_atoms=[], source_forms=[]),
            ]))


if __name__ == '__main__':
    unittest.main()
