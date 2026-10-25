"""Semantic regression fixtures for the release boundary; no Lean or network."""
import copy
import hashlib
import importlib.util
import io
import json
import pathlib
import tarfile
import unittest
import sys
from unittest import mock

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
spec = importlib.util.spec_from_file_location('release_guard', ROOT / 'scripts/check_release_packet.py')
guard = importlib.util.module_from_spec(spec);spec.loader.exec_module(guard)
OLD = '8ba7d5096d7d77a1e2f6e6f04ba70c85aed2a814'
NEW = '5ad14f00d92275a9e782fb9491dbfd8d8d8f9faf'
PROJECT = 'topology/collectionwise-normal'


class MaterialDefinitionHandoff(unittest.TestCase):
    PROJECT = 'topology/kuratowski-ulam'

    def setUp(self):
        package = ROOT / self.PROJECT
        self.files = {p.relative_to(package).as_posix(): p.read_bytes()
                      for p in package.rglob('*') if p.is_file() and
                      '.lake' not in p.relative_to(package).parts and
                      '__pycache__' not in p.relative_to(package).parts}

    def check(self):
        # Inventory-only fixtures do not certify the package's release prose.
        # Real frozen-status regressions below exercise that gate independently.
        with mock.patch.object(guard, 'snapshot', return_value=self.files), \
                mock.patch.object(guard, 'status_errors', return_value=[]):
            return guard.check_status(ROOT, '0' * 40, self.PROJECT)

    def test_complete_frozen_material_evidence_passes(self):
        self.check()

    def test_missing_inventory_blocks_frozen_handoff(self):
        del self.files['verification/material-imported-definitions.json']
        with self.assertRaises(ValueError):
            self.check()

    def test_stale_frozen_bridge_blocks_handoff(self):
        self.files['ChallengeTests.lean'] = b'module\n'
        with self.assertRaises(ValueError):
            self.check()


class LocallyCompactMaterialHandoff(MaterialDefinitionHandoff):
    PROJECT = 'topology/locally-compact-baire'


class BanachMazurMaterialHandoff(MaterialDefinitionHandoff):
    PROJECT = 'topology/banach-mazur-baire'


class ChoquetMaterialHandoff(MaterialDefinitionHandoff):
    PROJECT = 'topology/choquet-baire-product'


class CategoryGameMaterialHandoff(MaterialDefinitionHandoff):
    PROJECT = 'topology/banach-mazur-category'


class StrongChoquetMaterialHandoff(MaterialDefinitionHandoff):
    PROJECT = 'topology/strong-choquet-polish'


class HodgeMaterialHandoff(MaterialDefinitionHandoff):
    PROJECT = 'algebraic-hodge/ddbar-pilot'

    def test_stale_frozen_bridge_blocks_handoff(self):
        self.files['HodgeChallengeTests.lean'] = b'module\n'
        with self.assertRaises(ValueError):
            self.check()


class HodgeSourcePath(unittest.TestCase):
    def test_existing_frozen_hodge_source_is_supported(self):
        files = guard.snapshot(ROOT, 'c3107f8311488bcc256103db8ad969ffd60706e2',
                               'algebraic-hodge/ddbar-pilot')
        self.assertIn('HodgeChallenge.lean', files)

    def test_unknown_or_traversing_paths_are_rejected(self):
        for path in ['algebraic-hodge/other', 'algebraic-hodge/ddbar-pilot/../ddbar-pilot',
                     'topology/../algebraic-hodge/ddbar-pilot', '/algebraic-hodge/ddbar-pilot']:
            with self.subTest(path=path), self.assertRaisesRegex(ValueError, 'Invalid project path'):
                guard.snapshot(ROOT, '0' * 40, path)


class ComputationalHodgeMaterialHandoff(MaterialDefinitionHandoff):
    PROJECT = 'computational-hodge/finite-periods'

    def test_stale_frozen_bridge_blocks_handoff(self):
        self.files['ChallengeSemantics.lean'] = b'module\n'
        with self.assertRaises(ValueError):
            self.check()


class ComputationalHodgeSourcePath(unittest.TestCase):
    def test_exact_computational_hodge_path_is_supported(self):
        with mock.patch.object(guard.subprocess, 'check_output',
                               side_effect=[b'Challenge.lean\n', b'module\n']) as command:
            files = guard.snapshot(ROOT, '0' * 40, 'computational-hodge/finite-periods')
        self.assertEqual(files, {'Challenge.lean': b'module\n'})
        self.assertEqual(command.call_count, 2)
        self.assertEqual(command.call_args.args[0][-1],
                         '0' * 40 + ':computational-hodge/finite-periods/Challenge.lean')

    def test_other_or_traversing_computational_paths_are_rejected_before_git(self):
        with mock.patch.object(guard.subprocess, 'check_output') as command:
            for path in ['computational-hodge/other',
                         'computational-hodge/finite-periods/../finite-periods',
                         '/computational-hodge/finite-periods']:
                with self.subTest(path=path), self.assertRaisesRegex(ValueError, 'Invalid project path'):
                    guard.snapshot(ROOT, '0' * 40, path)
            command.assert_not_called()


class PresentationHomologyMaterialHandoff(ComputationalHodgeMaterialHandoff):
    PROJECT = 'computational-hodge/presentation-homology'


class PresentationHomologySourcePath(unittest.TestCase):
    def test_exact_presentation_homology_path_is_supported(self):
        with mock.patch.object(guard.subprocess, 'check_output',
                               side_effect=[b'Challenge.lean\n', b'module\n']) as command:
            files = guard.snapshot(ROOT, '0' * 40, 'computational-hodge/presentation-homology')
        self.assertEqual(files, {'Challenge.lean': b'module\n'})
        self.assertEqual(command.call_count, 2)
        self.assertEqual(command.call_args.args[0][-1],
                         '0' * 40 + ':computational-hodge/presentation-homology/Challenge.lean')

    def test_other_or_traversing_presentation_paths_rejected_before_git(self):
        with mock.patch.object(guard.subprocess, 'check_output') as command:
            for path in ['computational-hodge/presentation-homology/../finite-periods',
                         'computational-hodge/presentation-homology/other',
                         'computational-hodge/new-project', '/computational-hodge/presentation-homology']:
                with self.subTest(path=path), self.assertRaisesRegex(ValueError, 'Invalid project path'):
                    guard.snapshot(ROOT, '0' * 40, path)
            command.assert_not_called()


class GeometricDescentMaterialHandoff(ComputationalHodgeMaterialHandoff):
    PROJECT = 'computational-hodge/geometric-descent'


class GeometricDescentSourcePath(unittest.TestCase):
    def test_exact_geometric_descent_path_is_supported(self):
        with mock.patch.object(guard.subprocess, 'check_output',
                               side_effect=[b'Challenge.lean\n', b'module\n']) as command:
            files = guard.snapshot(ROOT, '0' * 40, 'computational-hodge/geometric-descent')
        self.assertEqual(files, {'Challenge.lean': b'module\n'})
        self.assertEqual(command.call_count, 2)
        self.assertEqual(command.call_args.args[0][-1],
                         '0' * 40 + ':computational-hodge/geometric-descent/Challenge.lean')

    def test_other_or_traversing_geometric_paths_rejected_before_git(self):
        with mock.patch.object(guard.subprocess, 'check_output') as command:
            for path in ['computational-hodge/geometric-descent/../finite-periods',
                         'computational-hodge/geometric-descent/other',
                         'computational-hodge/new-project', '/computational-hodge/geometric-descent']:
                with self.subTest(path=path), self.assertRaisesRegex(ValueError, 'Invalid project path'):
                    guard.snapshot(ROOT, '0' * 40, path)
            command.assert_not_called()


class GeometricObstructionMaterialHandoff(ComputationalHodgeMaterialHandoff):
    PROJECT = 'computational-hodge/geometric-obstruction'


class GeometricObstructionSourcePath(unittest.TestCase):
    def test_exact_geometric_obstruction_path_is_supported(self):
        with mock.patch.object(guard.subprocess, 'check_output',
                               side_effect=[b'Challenge.lean\n', b'module\n']) as command:
            files = guard.snapshot(ROOT, '0' * 40, 'computational-hodge/geometric-obstruction')
        self.assertEqual(files, {'Challenge.lean': b'module\n'})
        self.assertEqual(command.call_count, 2)
        self.assertEqual(command.call_args.args[0][-1],
                         '0' * 40 + ':computational-hodge/geometric-obstruction/Challenge.lean')

    def test_other_or_traversing_obstruction_paths_rejected_before_git(self):
        with mock.patch.object(guard.subprocess, 'check_output') as command:
            for path in ['computational-hodge/geometric-obstruction/../finite-periods',
                         'computational-hodge/geometric-obstruction/other',
                         'computational-hodge/new-project', '/computational-hodge/geometric-obstruction']:
                with self.subTest(path=path), self.assertRaisesRegex(ValueError, 'Invalid project path'):
                    guard.snapshot(ROOT, '0' * 40, path)
            command.assert_not_called()


class LoopCharactersMaterialHandoff(ComputationalHodgeMaterialHandoff):
    PROJECT = 'computational-hodge/loop-characters'


class LoopCharactersSourcePath(unittest.TestCase):
    def test_exact_loop_characters_path_is_supported(self):
        with mock.patch.object(guard.subprocess, 'check_output',
                               side_effect=[b'Challenge.lean\n', b'module\n']) as command:
            files = guard.snapshot(ROOT, '0' * 40, 'computational-hodge/loop-characters')
        self.assertEqual(files, {'Challenge.lean': b'module\n'})
        self.assertEqual(command.call_count, 2)
        self.assertEqual(command.call_args.args[0][-1],
                         '0' * 40 + ':computational-hodge/loop-characters/Challenge.lean')

    def test_other_or_traversing_loop_character_paths_rejected_before_git(self):
        with mock.patch.object(guard.subprocess, 'check_output') as command:
            for path in ['computational-hodge/loop-characters/../finite-periods',
                         'computational-hodge/loop-characters/other',
                         'computational-hodge/new-project', '/computational-hodge/loop-characters']:
                with self.subTest(path=path), self.assertRaisesRegex(ValueError, 'Invalid project path'):
                    guard.snapshot(ROOT, '0' * 40, path)
            command.assert_not_called()


class AdvisoryKernelAccount(unittest.TestCase):
    def fixture(self, status='declined', reason='unsupported-inductive', exit_code=2):
        attempt = dict(name='con-ron', status=status, reason=reason, exit_code=exit_code,
                       detail='Synthetic trusted-report consistency fixture, not an actual kernel run.',
                       argv=['/pinned/bin/con-ron', '--jobs=2', '--verified'], budget_seconds=1800)
        return dict(kernels=[{'name': 'nanoda'}], kernel_attempts=[attempt],
                    comparator_log_tail='nanoda kernel accepts the solution\n'
                    'Lean default kernel accepts the solution\nYour solution is okay!',
                    warnings=['con-ron declined (' + reason +
                              '); mandatory Lean and NanoDa checks passed.'])

    def check(self, report):
        guard.check_kernel_account(report, {'external_kernels': {'nanoda': ['/pinned/nanoda']}})

    def test_recognized_advisory_declines_preserve_only_actual_acceptance(self):
        for reason, code in [('unsupported-inductive', 2), ('fuel-exhausted', 3), ('capacity', None)]:
            with self.subTest(reason=reason):
                self.check(self.fixture(reason=reason, exit_code=code))

    def test_advisory_acceptance_requires_accepted_kernel_entry(self):
        report = self.fixture('accepted', 'complete', 0)
        with self.assertRaises(ValueError):
            self.check(report)
        report['kernels'].append({'name': 'con-ron'})
        self.check(report)

    def test_missing_mandatory_acceptance_is_rejected(self):
        report = self.fixture();report['kernels'] = []
        with self.assertRaises(ValueError):self.check(report)
        report = self.fixture();report['comparator_log_tail'] = 'Your solution is okay!'
        with self.assertRaises(ValueError):self.check(report)

    def test_rejections_unknown_errors_and_inconsistent_receipts_are_rejected(self):
        changes = [
            lambda r: r['kernel_attempts'][0].update(exit_code=1),
            lambda r: r['kernel_attempts'][0].update(reason='unrecognized-checker-result'),
            lambda r: r['kernel_attempts'][0].update(status='error'),
            lambda r: r['kernel_attempts'][0].update(status='accepted', reason='complete', exit_code=False),
            lambda r: r['kernel_attempts'][0].update(budget_seconds=1801),
            lambda r: r['kernel_attempts'][0].update(budget_seconds=True),
            lambda r: r['kernel_attempts'][0].update(argv=['/pinned/con-ron', '--jobs=2']),
            lambda r: r['kernel_attempts'][0].update(detail=''),
            lambda r: r.update(warnings=[]),
            lambda r: r.update(kernel_attempts=[]),
            lambda r: r['kernel_attempts'].append(copy.deepcopy(r['kernel_attempts'][0])),
            lambda r: r['kernels'].append({'name': 'con-ron'}),
            lambda r: r['kernels'].append({'name': 'other'}),
            lambda r: r['kernels'].append({'name': 'nanoda'}),
        ]
        for change in changes:
            report = self.fixture();change(report)
            with self.subTest(change=change), self.assertRaises(ValueError):self.check(report)

    def test_legacy_required_kernel_contract_is_not_relaxed(self):
        with self.assertRaisesRegex(ValueError, 'Missing independent kernel'):
            guard.check_kernel_account(self.fixture(),
                                       {'external_kernels': {'nanoda': [], 'con-ron': []}})


def archive(files):
    out = io.BytesIO()
    with tarfile.open(fileobj=out, mode='w') as tar:
        for name, body in files.items():
            info = tarfile.TarInfo(name);info.size = len(body);tar.addfile(info, io.BytesIO(body))
    return out.getvalue()


class ReleasePacketTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.original = json.loads((ROOT / 'catalog-evidence/collectionwise-2026-10-18/full-report.json').read_bytes())
        cls.files = guard.snapshot(ROOT, NEW, PROJECT)
        cls.fields = dict(repository=guard.REPOSITORY, commit=NEW, project_path=PROJECT,
                          comparator_config_path=PROJECT + '/comparator.json',
                          formalization_metadata_path=PROJECT + '/formalization.yaml')

    def fixture(self):
        # Synthetic report fixture, not a claim that NEW has an actual full run.
        report = copy.deepcopy(self.original)
        report['source']['commit'] = NEW
        report['formalization']['sha256'] = guard.sha(self.files['formalization.yaml'])
        return report

    def check_fixture(self, report=None, fields=None, files=None, data=None):
        report = self.fixture() if report is None else report
        body = json.dumps(report).encode()
        files = self.files if files is None else files
        with mock.patch.object(guard, 'snapshot', return_value=files):
            return guard.check_packet(ROOT, self.fields if fields is None else fields,
                body, guard.sha(body), archive(files) if data is None else data)

    def test_synthetic_complete_binding_positive(self):
        self.assertEqual(self.check_fixture()['status'], 'pass')

    def test_active_submission_hold_blocks_even_otherwise_complete_packet(self):
        packet = {'proposed_submission_fields': self.fields,
                  'submission_hold': {'active': True, 'prerequisite': 'Palomar approval of PR41 entry'}}
        body = json.dumps(self.fixture()).encode()
        with self.assertRaisesRegex(ValueError, 'Submission hold is active'):
            guard.check_packet(ROOT, packet, body, guard.sha(body), archive(self.files))

    def test_actual_historical_source_rejected_for_stale_packaged_claims(self):
        with self.assertRaisesRegex(ValueError, 'stale blanket'):
            guard.check_status(ROOT, OLD, PROJECT)

    def test_corrected_historical_account_positive(self):
        guard.check_status(ROOT, NEW, PROJECT, ROOT / 'catalog-evidence/collectionwise-2026-10-18/full-report.json')

    def test_actual_old_report_does_not_certify_new_source(self):
        with self.assertRaisesRegex(ValueError, 'Historical report'):
            self.check_fixture(report=self.original)

    def test_source_metadata_readme_and_linked_review_stale_claims(self):
        for name in ['formalization.yaml', 'README.md', 'REVIEW.md', 'VERIFICATION.md']:
            with self.subTest(file=name):
                files = dict(self.files)
                files[name] += b'\nCanonical protected Comparator and NanoDa checks remain unperformed for this package.\n'
                with self.assertRaisesRegex(ValueError, 'stale blanket'):
                    self.check_fixture(files=files)

    def test_unfulfilled_and_bold_unrun_stage_claims_rejected(self):
        for name in ['README.md', 'REVIEW.md', 'PLAN.md', 'RUN-PLAN.md']:
            for text in [b'Protected Comparator and NanoDa remain unfulfilled for this candidate.',
                         b'Canonical checks have **not** run for this package.']:
                with self.subTest(file=name, text=text):
                    self.assertTrue(guard.status_errors({name: text}))

    def test_frozen_hodge_unfulfilled_account_is_not_ready(self):
        files = guard.snapshot(ROOT, '7eec3b8c5864af8571fb9c0be3a5f8ce281d7cbb',
                               'algebraic-hodge/ddbar-pilot')
        self.assertIn('REVIEW.md: stale blanket pending/completion account', guard.status_errors(files))

    def test_truthful_later_source_and_visual_pending_positive(self):
        files = dict(self.files)
        files['README.md'] += b'\nCanonical rendering of a later source remains unperformed. Browser visual review remains pending.\n'
        self.assertFalse(guard.status_errors(files))

    def test_browser_word_does_not_exempt_false_mixed_stage_claim(self):
        text = b'Canonical full verification and browser visual review remain unperformed for this source.'
        self.assertTrue(guard.status_errors({'README.md': text}))
        separate = b'Canonical full verification passed. Browser visual review remains unperformed.'
        self.assertFalse(guard.status_errors({'README.md': separate}))

    def test_report_semantic_tampering_rejected_even_with_recomputed_fixture_digest(self):
        changes = {
            'metadata': lambda r: r['formalization'].update(sha256='0'*64),
            'Comparator': lambda r: r['comparator'].update(sha256='0'*64),
            'Challenge': lambda r: r['challenge'].update(sha256='0'*64),
            'lockfile': lambda r: r['lake_manifest'].update(sha256='0'*64),
            'toolchain': lambda r: r.update(lean_toolchain='leanprover/lean4:v4.0.0'),
            'source': lambda r: r['source'].update(commit=OLD),
            'project': lambda r: r['source'].update(project_path='topology/other'),
            'repository': lambda r: r['source'].update(repository='other/repository'),
            'trust': lambda r: r['challenge'].update(trust_level='low'),
            'dependency': lambda r: r['challenge'].update(untrusted_sources=['other']),
            'kernel': lambda r: r.update(kernels=[{'name': 'nanoda'}]),
            'acceptance': lambda r: r.update(comparator_log_tail='No acceptance recorded'),
            'status': lambda r: r.update(status='fail'),
            'error': lambda r: r.update(errors=['failure']),
        }
        for name, change in changes.items():
            with self.subTest(change=name):
                report = self.fixture();change(report)
                with self.assertRaises(ValueError):self.check_fixture(report=report)
        report = self.fixture();protected = json.loads(report['protected_config'])
        protected['definition_names'] = [];report['protected_config'] = json.dumps(protected)
        report['protected_config_sha256'] = guard.sha(report['protected_config'].encode())
        with self.assertRaisesRegex(ValueError, 'definition_names'):self.check_fixture(report=report)

    def test_copyable_metadata_path_mismatch(self):
        fields = dict(self.fields);fields['formalization_metadata_path'] = PROJECT + '/README.md'
        with self.assertRaisesRegex(ValueError, 'Wrong intake paths'):self.check_fixture(fields=fields)

    def test_archive_contains_old_metadata(self):
        files = dict(self.files);files['formalization.yaml'] = guard.snapshot(ROOT, OLD, PROJECT)['formalization.yaml']
        with self.assertRaisesRegex(ValueError, 'Archive source bytes differ'):self.check_fixture(data=archive(files))

    def test_archive_missing_and_extra_source_files(self):
        for extra in [False, True]:
            files = dict(self.files)
            if extra:files['unrelated.txt'] = b'not source'
            else:files.pop('README.md')
            with self.assertRaisesRegex(ValueError, 'Wrong archive source file set'):self.check_fixture(data=archive(files))


class SeparateVerifiedReplayTests(ReleasePacketTests):
    """Current schema-2 protocol; synthetic fixtures never claim an actual run."""

    def fixture(self):
        report = super().fixture()
        protected = json.loads(report['protected_config'])
        nanoda = ['/trusted/bin/nanoda_bin']
        conron = ['/trusted/con-ron', '--jobs=2', '--verified']
        protected['external_kernels'] = {'nanoda': nanoda}
        report['protected_config'] = json.dumps(protected)
        report['protected_config_sha256'] = guard.sha(report['protected_config'].encode())
        report.update(schema_version=2, phase='verification',
                      lean_toolchain='leanprover/lean4:v4.35.0-rc2',
                      kernels=[{'name': 'nanoda', 'argv': nanoda},
                               {'name': 'con-ron', 'argv': conron}],
                      kernel_attempts=[{'name': 'con-ron', 'status': 'accepted',
                          'reason': 'complete', 'exit_code': 0, 'argv': conron,
                          'budget_seconds': 100,
                          'detail': 'con-ron: accepted 18207 declarations (--verified) t=6.2s\n\n'
                              'con-ron: 1 inductive blocks modelled in-process: Lean.Syntax '
                              '(30 generated records, checked by the fold as declarations '
                              'and not counted as records of the file)'}])
        report['comparator_log_tail'] = report['comparator_log_tail'].replace(
            'con-ron kernel accepts the solution', '')
        report['con_ron_checker'] = {
            'source_toolchain': report['lean_toolchain'], 'kind': 'maintainer-pinned-release',
            'release_tag': 'v4.36.0-rc1',
            'release_commit': 'c9afcddf514a6772bd4d649f7cfc04eff0b9f15e',
            'archive_sha256': '26b3cea1a006ad419215520b8668dcd3f6a9eeba1a123756563a739f9c6274b2',
            'binary_sha256': '4e5616d94374cae37324dad2594f6230c2bb2297240249fc78ff508f3bc5acef',
            'archive_url': 'https://github.com/leanprover/lean4/releases/download/v4.36.0-rc1/lean-4.36.0-rc1-linux.tar.zst',
        }
        report.setdefault('tool_digests', {})['con-ron'] = report['con_ron_checker']['binary_sha256']
        return report

    def test_current_protocol_binds_three_actual_acceptances(self):
        report = self.fixture()
        files = dict(self.files)
        files['lean-toolchain'] = (report['lean_toolchain'] + '\n').encode()
        self.assertEqual(self.check_fixture(report=report, files=files)['status'], 'pass')

    def check_fixture(self, report=None, fields=None, files=None, data=None):
        report = self.fixture() if report is None else report
        if files is None:
            files = dict(self.files)
            files['lean-toolchain'] = b'leanprover/lean4:v4.35.0-rc2\n'
        return super().check_fixture(report, fields, files, data)

    def test_pinned_nat_ordering_diagnostic_preserves_verified_acceptance(self):
        note = ('con-ron: 2 declarations hoisted ahead of the pinned Nat operations '
                'they ground: Nat.mul._f, Nat.mul')
        for include_modelled in [False, True]:
            with self.subTest(include_modelled=include_modelled):
                report = self.fixture()
                attempt = report['kernel_attempts'][0]
                if not include_modelled:
                    attempt['detail'] = attempt['detail'].splitlines()[0]
                attempt['detail'] += '\n' + note
                self.assertEqual(self.check_fixture(report=report)['status'], 'pass')

    def test_nat_ordering_metadata_cannot_hide_an_invalid_replay(self):
        note = ('con-ron: 2 declarations hoisted ahead of the pinned Nat operations '
                'they ground: Nat.mul._f, Nat.mul')
        changes = {
            'wrong-count': lambda text: text + '\n' + note.replace('2 declarations', '1 declarations'),
            'wrong-name': lambda text: text + '\n' + note.replace('Nat.mul._f', 'Nat.add._f'),
            'duplicate': lambda text: text + '\n' + note + '\n' + note,
            'before-verdict': lambda text: note + '\n' + text,
            'before-modelled': lambda text: text.replace('\n\n', '\n' + note + '\n'),
            'trailing-note-garbage': lambda text: text + '\n' + note + ' ignored',
            'unknown-checker-line': lambda text: text + '\n' + note + '\ncon-ron: unknown',
            'unprefixed-garbage': lambda text: text + '\n' + note + '\nignored failure text',
            'repeated-verdict': lambda text: text + '\n' + note + '\n' + text.splitlines()[0],
            'missing-verdict': lambda text: '\n'.join(text.splitlines()[2:]) + '\n' + note,
        }
        for name, change in changes.items():
            with self.subTest(change=name):
                report = self.fixture()
                report['kernel_attempts'][0]['detail'] = change(report['kernel_attempts'][0]['detail'])
                with self.assertRaisesRegex(ValueError, 'unambiguous'):
                    self.check_fixture(report=report)
        for name, change in {
            'nonzero': lambda r: r['kernel_attempts'][0].update(exit_code=1),
            'declined': lambda r: r['kernel_attempts'][0].update(status='declined'),
            'wrong-binary': lambda r: r['tool_digests'].update({'con-ron': '0' * 64}),
            'wrong-release': lambda r: r['con_ron_checker'].update(release_tag='v4.35.0-rc2'),
        }.items():
            with self.subTest(change=name):
                report = self.fixture()
                report['kernel_attempts'][0]['detail'] += '\n' + note
                change(report)
                with self.assertRaises(ValueError):
                    self.check_fixture(report=report)

    def test_replay_decline_or_ambiguous_acceptance_is_not_three_kernel_pass(self):
        changes = {
            'missing': lambda r: r.update(kernel_attempts=[]),
            'duplicate': lambda r: r['kernel_attempts'].append(copy.deepcopy(r['kernel_attempts'][0])),
            'declined': lambda r: r['kernel_attempts'][0].update(status='declined', reason='capacity'),
            'nonzero': lambda r: r['kernel_attempts'][0].update(exit_code=1),
            'boolean': lambda r: r['kernel_attempts'][0].update(exit_code=False),
            'unverified': lambda r: r['kernel_attempts'][0].update(argv=['/trusted/con-ron', '--jobs=2']),
            'argv-mismatch': lambda r: r['kernels'][1].update(argv=['/other/con-ron', '--jobs=2', '--verified']),
            'false-detail': lambda r: r['kernel_attempts'][0].update(detail='con-ron: rejected'),
            'mixed-detail': lambda r: r['kernel_attempts'][0].update(detail=r['kernel_attempts'][0]['detail']+'\n con-ron: declined'),
            'declined-verdict': lambda r: r['kernel_attempts'][0].update(detail=r['kernel_attempts'][0]['detail']+'\ncon-ron: declined: unsupported inductive example'),
            'rejected-verdict': lambda r: r['kernel_attempts'][0].update(detail=r['kernel_attempts'][0]['detail']+'\ncon-ron: rejected: invalid declaration'),
            'duplicate-verdict': lambda r: r['kernel_attempts'][0].update(detail=r['kernel_attempts'][0]['detail']+'\ncon-ron: accepted 1 declarations (--verified)'),
            'unknown-diagnostic': lambda r: r['kernel_attempts'][0].update(detail=r['kernel_attempts'][0]['detail']+'\ncon-ron: unknown'),
            'duplicate-kernel': lambda r: r['kernels'].append(copy.deepcopy(r['kernels'][1])),
            'wrong-digest': lambda r: r['tool_digests'].update({'con-ron':'0'*64}),
            'wrong-release': lambda r: r['con_ron_checker'].update(release_tag='v4.35.0-rc2'),
            'wrong-kind': lambda r: r['con_ron_checker'].update(kind='bundled'),
            'wrong-phase': lambda r: r.update(phase='preparation'),
            'wrong-schema': lambda r: r.update(schema_version=1),
            'zero-budget': lambda r: r['kernel_attempts'][0].update(budget_seconds=0),
        }
        for name, change in changes.items():
            with self.subTest(change=name):
                report = self.fixture();change(report)
                with self.assertRaises(ValueError):self.check_fixture(report=report)


if __name__ == '__main__':
    unittest.main()
