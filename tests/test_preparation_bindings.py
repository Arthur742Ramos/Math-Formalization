"""Reject misleading pointers to the correctly preserved source-bound full report."""
import copy
import json
import pathlib
import sys
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from check_preparations import check_status_correction, check_verified, check_user_submission_report, check_unconfirmed_intake, check_material_definition_correction, check_locally_compact_definition_preparation


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


class ImportedDefinitionCorrectionBindings(unittest.TestCase):
    def setUp(self):
        rows = json.loads((ROOT / 'PREPARATIONS.json').read_text())['projects']
        self.row = copy.deepcopy(next(p for p in rows if p['path'] == 'topology/kuratowski-ulam'))

    def check(self):
        source = self.row['source_snapshot']
        check_material_definition_correction(self.row, source['commit'], source['tree'])

    def test_actual_correction_preserves_old_pass_as_history(self):
        self.check()

    def test_old_pass_cannot_verify_current_source(self):
        self.row['canonical_full'] = 'pass'
        with self.assertRaises(AssertionError):
            self.check()

    def test_changed_proof_cannot_be_added_to_allowed_delta(self):
        self.row['definition_evidence_correction']['allowed_changed_files'].append('KUChallenge.lean')
        with self.assertRaises(AssertionError):
            self.check()

    def test_wrong_old_report_digest_rejected(self):
        old = self.row['definition_evidence_correction']['prior_verified_snapshot']
        old['full']['report_sha256'] = '0' * 64
        with self.assertRaises(AssertionError):
            self.check()

    def test_wrong_rendering_run_rejected(self):
        old = self.row['definition_evidence_correction']['prior_verified_snapshot']
        old['rendering']['url'] = 'https://github.com/Arthur742Ramos/Math-Formalization/actions/runs/1'
        with self.assertRaises(AssertionError):
            self.check()

    def test_runner_approval_cannot_transfer(self):
        self.row['fresh_runner_security_approval'] = True
        with self.assertRaises(AssertionError):
            self.check()

    def test_historical_run_id_must_match_bound_url(self):
        for kind in ['full', 'rendering']:
            with self.subTest(kind=kind):
                old = self.row['definition_evidence_correction']['prior_verified_snapshot'][kind]
                run_id = old['run_id']
                old['run_id'] = 1
                with self.assertRaises(AssertionError):
                    self.check()
                old['run_id'] = run_id

    def test_historical_attempt_cannot_be_invented(self):
        for kind in ['full', 'rendering']:
            with self.subTest(kind=kind):
                old = self.row['definition_evidence_correction']['prior_verified_snapshot'][kind]
                old['attempt'] = 2
                with self.assertRaises(AssertionError):
                    self.check()
                old['attempt'] = 1

    def test_historical_status_must_match_pass_report(self):
        for kind in ['full', 'rendering']:
            with self.subTest(kind=kind):
                old = self.row['definition_evidence_correction']['prior_verified_snapshot'][kind]
                old['status'] = 'failed'
                with self.assertRaises(AssertionError):
                    self.check()
                old['status'] = 'pass'


class LocallyCompactDefinitionBindings(unittest.TestCase):
    def setUp(self):
        rows = json.loads((ROOT / 'PREPARATIONS.json').read_text())['projects']
        self.row = copy.deepcopy(next(p for p in rows if p['path'] == 'topology/locally-compact-baire'))

    def check(self):
        source = self.row['source_snapshot']
        check_locally_compact_definition_preparation(self.row, source['commit'], source['tree'])

    def test_actual_prior_ordinary_history_and_new_audit_pass(self):
        self.check()

    def test_prior_run_id_cannot_be_fabricated(self):
        self.row['prior_ordinary_source']['lean_run'] = 1
        with self.assertRaises(AssertionError): self.check()

    def test_prior_attempt_cannot_be_invented(self):
        self.row['prior_ordinary_source']['attempts'] = 2
        with self.assertRaises(AssertionError): self.check()

    def test_prior_source_cannot_be_substituted(self):
        self.row['prior_ordinary_source']['source_commit'] = self.row['source_snapshot']['commit']
        with self.assertRaises(AssertionError): self.check()

    def test_wrong_old_package_tree_rejected(self):
        self.row['prior_ordinary_source']['package_tree'] = '0' * 40
        with self.assertRaises(AssertionError): self.check()

    def test_provider_digest_cannot_be_relabelled(self):
        self.row['prior_ordinary_source']['provider_record_sha256'] = '0' * 64
        with self.assertRaises(AssertionError): self.check()

    def test_failed_history_cannot_be_called_success(self):
        self.row['prior_ordinary_source']['conclusion'] = 'failure'
        with self.assertRaises(AssertionError): self.check()

    def test_audit_bound_to_wrong_source_rejected(self):
        self.row['material_definition_audit']['source_commit'] = '0' * 40
        with self.assertRaises(AssertionError): self.check()

    def test_audit_inventory_count_cannot_be_fabricated(self):
        self.row['material_definition_audit']['material_declarations'] = 1
        with self.assertRaises(AssertionError): self.check()

    def test_audit_excerpt_count_cannot_be_fabricated(self):
        self.row['material_definition_audit']['literal_excerpts'] = 1
        with self.assertRaises(AssertionError): self.check()

    def test_old_ordinary_pass_cannot_establish_new_canonical_pass(self):
        self.row['canonical_full'] = 'pass'
        with self.assertRaises(AssertionError): self.check()

    def test_prior_security_approval_cannot_transfer(self):
        self.row['fresh_runner_security_approval'] = True
        with self.assertRaises(AssertionError): self.check()


if __name__ == '__main__':
    unittest.main()
