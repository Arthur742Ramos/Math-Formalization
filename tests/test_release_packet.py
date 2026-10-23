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
        with mock.patch.object(guard, 'snapshot', return_value=self.files):
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
