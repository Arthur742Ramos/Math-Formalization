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


if __name__ == '__main__':
    unittest.main()
