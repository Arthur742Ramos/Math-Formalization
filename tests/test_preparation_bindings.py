"""Reject misleading pointers to the correctly preserved source-bound full report."""
import copy
import json
import pathlib
import sys
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from check_preparations import check_status_correction, check_verified, check_user_submission_report, check_unconfirmed_intake


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


class ReportedSubmissionBindings(unittest.TestCase):
    def setUp(self):
        rows = json.loads((ROOT / 'PREPARATIONS.json').read_text())['projects']
        self.row = copy.deepcopy(next(p for p in rows if p['path'] == 'topology/sigma-product-compactness'))

    def check(self):
        source = self.row['source_snapshot']
        check_verified(self.row, ROOT / self.row['path'], source['commit'], source['tree'])

    def test_completed_evidence_and_reported_submission_pass(self):
        self.check()

    def test_unverified_registration_cannot_be_promoted(self):
        self.row['latest_user_report']['registration'] = 'registered'
        with self.assertRaises(AssertionError):
            check_user_submission_report(self.row)

    def test_old_runner_approval_cannot_transfer(self):
        self.row['fresh_runner_security_approval'] = True
        with self.assertRaises(AssertionError):
            check_user_submission_report(self.row)

    def test_wrong_completed_run_rejected(self):
        full = self.row['canonical_run']
        full['run_id'] = 1
        full['url'] = 'https://github.com/Arthur742Ramos/Math-Formalization/actions/runs/1'
        with self.assertRaises(AssertionError):
            self.check()

    def test_second_attempt_not_invented(self):
        self.row['canonical_run']['attempt'] = 2
        with self.assertRaises(AssertionError):
            self.check()


class UnconfirmedIntakeBindings(unittest.TestCase):
    def setUp(self):
        rows = json.loads((ROOT / 'PREPARATIONS.json').read_text())['projects']
        self.row = copy.deepcopy(next(p for p in rows if p['path'] == 'topology/product-countable-chain-condition'))

    def check(self):
        source = self.row['source_snapshot']
        check_verified(self.row, ROOT / self.row['path'], source['commit'], source['tree'])

    def test_actual_completed_evidence_with_unconfirmed_intake_passes(self):
        self.check()

    def test_completed_checks_do_not_establish_intake(self):
        self.row['registry_intake_status'] = 'submitted'
        with self.assertRaises(AssertionError):
            check_unconfirmed_intake(self.row)

    def test_completed_checks_do_not_establish_registration(self):
        self.row['registry_registration_status'] = 'registered'
        with self.assertRaises(AssertionError):
            check_unconfirmed_intake(self.row)

    def test_consumed_runner_approval_cannot_transfer(self):
        self.row['fresh_runner_security_approval'] = True
        with self.assertRaises(AssertionError):
            check_unconfirmed_intake(self.row)

    def test_wrong_source_report_cannot_transfer(self):
        self.row['canonical_run']['verified_source_commit'] = 'dd4675197cac51f2de3fc0ab66195cb0807023dc'
        with self.assertRaises(AssertionError):
            self.check()


class KuratowskiUlamUnconfirmedBindings(UnconfirmedIntakeBindings):
    def setUp(self):
        rows = json.loads((ROOT / 'PREPARATIONS.json').read_text())['projects']
        self.row = copy.deepcopy(next(p for p in rows if p['path'] == 'topology/kuratowski-ulam'))

    def test_wrong_source_report_cannot_transfer(self):
        self.row['canonical_run']['verified_source_commit'] = '92f1a925329465c86a96b2f612fcd0d5345eed3b'
        with self.assertRaises(AssertionError):
            self.check()


if __name__ == '__main__':
    unittest.main()
