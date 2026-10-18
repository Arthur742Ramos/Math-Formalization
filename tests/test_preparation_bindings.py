"""Reject misleading pointers to the correctly preserved source-bound full report."""
import copy
import json
import pathlib
import sys
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from check_preparations import check_status_correction


class CorrectedFullBindings(unittest.TestCase):
    def setUp(self):
        row = json.loads((ROOT / 'PREPARATIONS.json').read_text())['projects'][0]
        self.row = copy.deepcopy(row)

    def check(self):
        source = self.row['source_snapshot']
        check_status_correction(self.row, source['commit'], source['tree'])

    def test_actual_source_bound_run_passes(self):
        self.check()

    def test_wrong_run_pointer_rejected(self):
        full = self.row['current_source_full_run']
        full['run_id'] = 1
        full['url'] = 'https://github.com/Arthur742Ramos/Math-Formalization/actions/runs/1'
        with self.assertRaises(AssertionError):
            self.check()

    def test_foreign_repository_rejected(self):
        full = self.row['current_source_full_run']
        full['repository'] = 'example/other'
        full['url'] = 'https://github.com/example/other/actions/runs/39142937826'
        with self.assertRaises(AssertionError):
            self.check()

    def test_unobserved_attempt_rejected(self):
        self.row['current_source_full_run']['attempt'] = 2
        with self.assertRaises(AssertionError):
            self.check()


if __name__ == '__main__':
    unittest.main()
