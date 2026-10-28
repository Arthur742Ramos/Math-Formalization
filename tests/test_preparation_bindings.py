"""Reject misleading pointers to the correctly preserved source-bound full report."""
import copy
import json
import pathlib
import os
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from check_preparations import check_status_correction, check_verified, check_user_submission_report, check_unconfirmed_intake, check_user_registration_report, check_material_definition_correction, check_locally_compact_definition_preparation, check_material_audit_binding
import check_preparations as prep


class NarrowStatusCorrectionBindings(unittest.TestCase):
    def setUp(self):
        self.old = {'README.md': b'old', 'formalization.yaml': json.dumps({
            'project': {'authors': ['A']}, 'status': {'known_gaps': 'old'},
            'review': {'notes': 'old'}}).encode(), 'Proof.lean': b'proof',
            'comparator.json': b'{}', 'lean-toolchain': b'lean', 'lake-manifest.json': b'{}'}
        self.new = dict(self.old, **{'README.md': b'new'})
        self.old_modes = {name: '100644' for name in self.old}
        self.new_modes = dict(self.old_modes)
        self.trees = {'old:topology/example': 'oldtree', 'verified:topology/example': 'oldtree',
                      'corrected:topology/example': 'newtree', 'HEAD:topology/example': 'newtree'}
        self.p = {'path': 'topology/example', 'state': 'reviewed-preparation-not-submitted',
                  'current_source_snapshot': {'commit': 'corrected', 'tree': 'newtree'},
                  'current_source_full': 'not-established', 'current_source_rendering': 'not-established',
                  'status_correction': {'kind': 'narrow-status-only-evidence-carry',
                    'historical_source': 'old', 'historical_evidence_source': 'verified',
                    'corrected_source': 'corrected', 'corrected_tree': 'newtree',
                    'changed_files': ['README.md']}}

    def check(self):
        def git(_operation, name): return self.trees[name]
        def snapshot(_root, commit, _project): return self.old if commit == 'old' else self.new
        def modes(_root, commit, _project): return self.old_modes if commit == 'old' else self.new_modes
        with mock.patch.object(prep, 'git', side_effect=git), mock.patch.object(prep, 'snapshot', side_effect=snapshot), \
             mock.patch.object(prep, 'modes', side_effect=modes), mock.patch.object(prep.subprocess, 'run'):
            check_status_correction(self.p, 'old', 'oldtree')

    def test_status_only_correction_binds_old_and_new_trees(self):
        self.check()

    def test_changed_proof_configuration_or_mode_is_rejected(self):
        for name in ('Proof.lean', 'comparator.json', 'lean-toolchain', 'lake-manifest.json'):
            with self.subTest(name=name):
                value = self.new[name]; self.new[name] += b'changed'
                with self.assertRaises(ValueError): self.check()
                self.new[name] = value
        self.new_modes['Proof.lean'] = '100755'
        with self.assertRaises(ValueError): self.check()

    def test_file_set_and_non_status_metadata_changes_are_rejected(self):
        self.new['extra.lean'] = b'theorem extra'
        with self.assertRaises(ValueError): self.check()
        del self.new['extra.lean']
        meta = json.loads(self.new['formalization.yaml'])
        meta['project']['authors'] = ['B']
        self.new['formalization.yaml'] = json.dumps(meta).encode()
        with self.assertRaises(ValueError): self.check()

    def test_evidence_and_current_tree_cannot_be_misbound(self):
        for key in ('verified:topology/example', 'corrected:topology/example', 'HEAD:topology/example'):
            with self.subTest(key=key):
                value = self.trees[key]; self.trees[key] = 'wrong'
                with self.assertRaises(AssertionError): self.check()
                self.trees[key] = value
        self.p['current_source_full'] = 'pass'
        with self.assertRaises(AssertionError): self.check()

    def test_nonancestor_is_rejected(self):
        import subprocess
        for pair in [('old', 'verified'), ('verified', 'corrected'), ('corrected', 'HEAD')]:
            def reject_pair(argv, **_kwargs):
                if tuple(argv[-2:]) == pair:
                    raise subprocess.CalledProcessError(1, argv)
            with self.subTest(pair=pair), \
                 mock.patch.object(prep, 'git', side_effect=lambda _op, name: self.trees[name]), \
                 mock.patch.object(prep.subprocess, 'run', side_effect=reject_pair):
                with self.assertRaises(subprocess.CalledProcessError):
                    check_status_correction(self.p, 'old', 'oldtree')

    def test_merged_sibling_evidence_is_not_a_lineage(self):
        with tempfile.TemporaryDirectory() as folder:
            root = pathlib.Path(folder)
            env = dict(os.environ, GIT_AUTHOR_NAME='Test', GIT_AUTHOR_EMAIL='test@example.invalid',
                       GIT_COMMITTER_NAME='Test', GIT_COMMITTER_EMAIL='test@example.invalid')
            def git(*args):
                return subprocess.check_output(['git', '-C', folder, *args], env=env, text=True,
                                               stderr=subprocess.DEVNULL).strip()
            git('init', '-q')
            project = root / 'topology/example'; project.mkdir(parents=True)
            for name, data in self.old.items(): (project / name).write_bytes(data)
            git('add', '.'); git('commit', '-qm', 'checkpoint')
            old, oldtree = git('rev-parse', 'HEAD'), git('rev-parse', 'HEAD:topology/example')
            (root / 'evidence-marker').write_text('evidence')
            git('add', '.'); git('commit', '-qm', 'verified')
            verified = git('rev-parse', 'HEAD')
            git('checkout', '-q', '--detach', old)
            (project / 'README.md').write_bytes(b'new')
            git('add', '.'); git('commit', '-qm', 'correction')
            corrected, newtree = git('rev-parse', 'HEAD'), git('rev-parse', 'HEAD:topology/example')
            git('merge', '-q', '--no-ff', '-m', 'merge sibling', verified)
            p = copy.deepcopy(self.p)
            p['current_source_snapshot'] = {'commit': corrected, 'tree': newtree}
            p['status_correction'].update(historical_source=old, historical_evidence_source=verified,
                                          corrected_source=corrected, corrected_tree=newtree)
            with mock.patch.object(prep, 'ROOT', root):
                with self.assertRaises(subprocess.CalledProcessError):
                    check_status_correction(p, old, oldtree)


class FixedGameAuditBindings(unittest.TestCase):
    def setUp(self):
        rows = json.loads((ROOT / 'PREPARATIONS.json').read_text())['projects']
        self.row = copy.deepcopy(next(p for p in rows if p['path'] == 'topology/banach-mazur-baire'))

    def check(self):
        check_material_audit_binding(self.row, self.row['source_snapshot']['commit'])

    def test_exact_fixed_model_and_material_evidence_pass(self):
        self.check()

    def test_entire_required_audit_cannot_be_removed(self):
        del self.row['material_definition_audit']
        with self.assertRaises(AssertionError): self.check()

    def test_wrong_source_cannot_borrow_audit(self):
        self.row['material_definition_audit']['source_commit'] = '0' * 40
        with self.assertRaises(AssertionError): self.check()

    def test_fabricated_inventory_counts_rejected(self):
        for key in ['material_declarations', 'upstream_files', 'literal_excerpts']:
            with self.subTest(key=key):
                old = self.row['material_definition_audit'][key]
                self.row['material_definition_audit'][key] = 999
                with self.assertRaises(AssertionError): self.check()
                self.row['material_definition_audit'][key] = old

    def test_wrong_schema_rejected(self):
        self.row['material_definition_audit']['schema_version'] = 1
        with self.assertRaises(AssertionError): self.check()

    def test_missing_independent_entrypoint_rejected(self):
        self.row['material_definition_audit']['semantic_tests'].pop()
        with self.assertRaises(AssertionError): self.check()

    def test_wrong_fixed_model_names_rejected(self):
        self.row['fixed_model_definitions'] = ['False']
        with self.assertRaises(AssertionError): self.check()

    def test_game_definition_holes_rejected(self):
        self.row['definition_names'] = self.row['fixed_model_definitions']
        with self.assertRaises(AssertionError): self.check()

    def test_task_zero_intakes_cannot_establish_private_absence(self):
        self.row['registry_intake_status'] = 'none'
        with self.assertRaises(AssertionError): self.check()

    def test_proof_checks_cannot_establish_registration(self):
        self.row['registry_registration_status'] = 'registered'
        with self.assertRaises(AssertionError): self.check()


class ChoquetFixedGameAuditBindings(FixedGameAuditBindings):
    def setUp(self):
        rows = json.loads((ROOT / 'PREPARATIONS.json').read_text())['projects']
        self.row = copy.deepcopy(next(p for p in rows if p['path'] == 'topology/choquet-baire-product'))


class CategoryGameFixedAuditBindings(FixedGameAuditBindings):
    def setUp(self):
        rows = json.loads((ROOT / 'PREPARATIONS.json').read_text())['projects']
        self.row = copy.deepcopy(next(p for p in rows if p['path'] == 'topology/banach-mazur-category'))


class StrongChoquetFixedAuditBindings(FixedGameAuditBindings):
    def setUp(self):
        rows = json.loads((ROOT / 'PREPARATIONS.json').read_text())['projects']
        self.row = copy.deepcopy(next(p for p in rows if p['path'] == 'topology/strong-choquet-polish'))


class UserRegistrationReportBindings(unittest.TestCase):
    def setUp(self):
        rows = json.loads((ROOT / 'PREPARATIONS.json').read_text())['projects']
        self.row = copy.deepcopy(next(p for p in rows if p['path'] == 'topology/banach-mazur-category'))

    def test_explicit_user_report_preserves_unknown_public_id(self):
        check_user_registration_report(self.row)

    def test_missing_report_is_not_registration_evidence(self):
        del self.row['latest_user_report']
        with self.assertRaises(KeyError): check_user_registration_report(self.row)

    def test_machine_checks_cannot_replace_user_report(self):
        self.row['latest_user_report']['actor'] = 'CI'
        with self.assertRaises(AssertionError): check_user_registration_report(self.row)

    def test_wrong_source_report_rejected(self):
        self.row['latest_user_report']['source_commit'] = '0' * 40
        with self.assertRaises(AssertionError): check_user_registration_report(self.row)

    def test_unverified_public_id_cannot_be_invented(self):
        self.row['latest_user_report']['public_registration_id'] = 'PALOMAR-2026-10-20-000001'
        with self.assertRaises(AssertionError): check_user_registration_report(self.row)

    def test_report_is_not_independent_public_confirmation(self):
        self.row['latest_user_report']['classification'] = 'independently-verified-registered'
        with self.assertRaises(AssertionError): check_user_registration_report(self.row)

    def test_consumed_security_approval_does_not_transfer(self):
        self.row['fresh_runner_security_approval'] = True
        with self.assertRaises(AssertionError): check_user_registration_report(self.row)


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
        self.row['state'] = 'reviewed-preparation-not-submitted'
        self.row['canonical_full'] = 'pass'
        with self.assertRaises(AssertionError): self.check()

    def test_prior_security_approval_cannot_transfer(self):
        self.row['fresh_runner_security_approval'] = True
        with self.assertRaises(AssertionError): self.check()

    def test_completed_full_cannot_use_old_ordinary_source(self):
        self.row['canonical_run']['verified_source_commit'] = self.row['prior_ordinary_source']['source_commit']
        with self.assertRaises(AssertionError): self.check()

    def test_completed_full_cannot_use_ordinary_run_pointer(self):
        self.row['canonical_run']['run_id'] = self.row['prior_ordinary_source']['lean_run']
        with self.assertRaises(AssertionError): self.check()

    def test_completed_render_cannot_use_different_source(self):
        self.row['rendering_run']['verified_source_commit'] = '0' * 40
        with self.assertRaises(AssertionError): self.check()


class VerifiedGameFullBindings(unittest.TestCase):
    def setUp(self):
        rows = json.loads((ROOT / 'PREPARATIONS.json').read_text())['projects']
        self.row = copy.deepcopy(next(p for p in rows if p['path'] == 'topology/banach-mazur-baire'))

    def check(self):
        source = self.row['source_snapshot']
        check_material_audit_binding(self.row, source['commit'])
        check_verified(self.row, ROOT / self.row['path'], source['commit'], source['tree'])

    def test_actual_original_full_and_renderer_bind(self):
        self.check()

    def test_ordinary_run_cannot_replace_protected_full(self):
        self.row['canonical_run']['run_id'] = 39326670168
        self.row['canonical_run']['url'] = 'https://github.com/Arthur742Ramos/Math-Formalization/actions/runs/39326670168'
        with self.assertRaises(AssertionError): self.check()

    def test_equal_package_tree_does_not_change_tested_commit(self):
        self.row['canonical_run']['verified_source_commit'] = 'e5da90e7f29da2ce1270a1ada54ff39e782dba74'
        with self.assertRaises(AssertionError): self.check()

    def test_unobserved_request_cannot_borrow_report(self):
        self.row['canonical_run']['request_id'] = 'bmfull000002'
        with self.assertRaises(AssertionError): self.check()

    def test_original_render_digest_cannot_be_relabelled(self):
        self.row['rendering_run']['original_report_sha256'] = '0' * 64
        with self.assertRaises(AssertionError): self.check()


if __name__ == '__main__':
    unittest.main()
