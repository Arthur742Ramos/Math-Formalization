"""Offline cyclic release-boundary fixtures, never claims of actual kernel runs."""
import copy
import importlib.util
import io
import json
import pathlib
import sys
import tarfile
import unittest
from unittest import mock

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
spec = importlib.util.spec_from_file_location('cyclic_release_guard', ROOT / 'scripts/check_release_packet.py')
guard = importlib.util.module_from_spec(spec)
spec.loader.exec_module(guard)
PROJECT = 'combinatorics/cyclic-covering-certificates'
SOURCE = 'a7cf88ed29255aea5e0c562bd392cf892da4a701'


def archive(files):
    output = io.BytesIO()
    with tarfile.open(fileobj=output, mode='w') as bundle:
        for name, body in files.items():
            entry = tarfile.TarInfo(name)
            entry.size = len(body)
            bundle.addfile(entry, io.BytesIO(body))
    return output.getvalue()


class CyclicSourcePath(unittest.TestCase):
    def test_exact_frozen_source_is_supported(self):
        files = guard.snapshot(ROOT, SOURCE, PROJECT)
        self.assertIn('Challenge.lean', files)
        self.assertIn('Solution.lean', files)

    def test_nearby_absolute_and_traversing_paths_rejected_before_git(self):
        paths = [PROJECT + '/other', PROJECT + '-extra', PROJECT + '/',
                 PROJECT + '/../cyclic-covering-certificates', '/' + PROJECT,
                 './' + PROJECT, 'combinatorics/other',
                 'topology/../' + PROJECT, PROJECT + '\n']
        with mock.patch.object(guard.subprocess, 'check_output') as command:
            for path in paths:
                with self.subTest(path=path), self.assertRaisesRegex(ValueError, 'Invalid project path'):
                    guard.snapshot(ROOT, SOURCE, path)
            command.assert_not_called()

    def test_symbolic_source_is_rejected_before_git(self):
        with mock.patch.object(guard.subprocess, 'check_output') as command:
            with self.assertRaisesRegex(ValueError, 'exact source commit'):
                guard.snapshot(ROOT, 'HEAD', PROJECT)
            command.assert_not_called()

    def test_status_only_does_not_require_future_evidence_or_authorize_intake(self):
        # Existing prose states requirements, not fictional future successes.
        self.assertEqual(guard.check_status(ROOT, SOURCE, PROJECT), guard.snapshot(ROOT, SOURCE, PROJECT))


class CyclicReleasePacket(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.files = guard.snapshot(ROOT, SOURCE, PROJECT)
        cls.fields = dict(repository=guard.REPOSITORY, commit=SOURCE, project_path=PROJECT,
                          comparator_config_path=PROJECT + '/comparator.json',
                          formalization_metadata_path=PROJECT + '/formalization.yaml')

    def fixture(self, reason='unsupported-inductive', exit_code=2):
        config = json.loads(self.files['comparator.json'])
        protected = {key: config[key] for key in ('theorem_names', 'definition_names', 'permitted_axioms',
                                                'challenge_module', 'solution_module')}
        protected.update(challenge_module='PalomarCanonicalSynthetic.Challenge',
                         external_kernels={'nanoda': ['/synthetic/bin/nanoda_bin']})
        report = dict(schema_version=2, phase='verification', execution_profile='palomar-standard-v1',
                      status='pass', stage='complete', errors=[],
                      source=dict(repository=guard.REPOSITORY, commit=SOURCE, project_path=PROJECT),
                      lean_toolchain=self.files['lean-toolchain'].decode().strip(),
                      protected_config=json.dumps(protected),
                      kernels=[{'name': 'nanoda', 'argv': protected['external_kernels']['nanoda']}],
                      kernel_attempts=[dict(name='con-ron', status='declined', reason=reason,
                          exit_code=exit_code, argv=['/synthetic/con-ron', '--jobs=2', '--verified'],
                          budget_seconds=1800,
                          detail='Synthetic recognized support/capacity decline, not an actual run.')],
                      warnings=['con-ron declined (' + reason + '); mandatory Lean and NanoDa checks passed.'],
                      comparator_log_tail='nanoda kernel accepts the solution\n'
                          'Lean default kernel accepts the solution\nYour solution is okay!')
        for kind, name in dict(formalization='formalization.yaml', comparator='comparator.json',
                               challenge='Challenge.lean', solution='Solution.lean', lakefile='lakefile.toml',
                               lake_manifest='lake-manifest.json').items():
            report[kind] = dict(path=PROJECT + '/' + name, sha256=guard.sha(self.files[name]))
        for key in ('theorem_names', 'definition_names', 'permitted_axioms'):
            report['comparator'][key] = config[key]
        for kind in ('challenge', 'solution'):
            report[kind]['module'] = config[kind + '_module']
        report['challenge'].update(trust_level='high', untrusted_sources=[])
        report['protected_config_sha256'] = guard.sha(report['protected_config'].encode())
        return report

    def accepted_fixture(self):
        report = self.fixture()
        attempt = report['kernel_attempts'][0]
        attempt.update(status='accepted', reason='complete', exit_code=0,
                       detail='con-ron: accepted 123 declarations (--verified)')
        report['kernels'].append({'name': 'con-ron', 'argv': attempt['argv']})
        report['warnings'] = []
        report['con_ron_checker'] = {
            'source_toolchain': report['lean_toolchain'], 'kind': 'maintainer-pinned-release',
            'release_tag': 'v4.36.0-rc1',
            'release_commit': 'c9afcddf514a6772bd4d649f7cfc04eff0b9f15e',
            'archive_sha256': '26b3cea1a006ad419215520b8668dcd3f6a9eeba1a123756563a739f9c6274b2',
            'binary_sha256': '4e5616d94374cae37324dad2594f6230c2bb2297240249fc78ff508f3bc5acef',
            'archive_url': 'https://github.com/leanprover/lean4/releases/download/v4.36.0-rc1/lean-4.36.0-rc1-linux.tar.zst',
        }
        report['tool_digests'] = {'con-ron': report['con_ron_checker']['binary_sha256']}
        return report

    def check(self, report=None, fields=None, files=None, data=None, digest=None):
        report = self.fixture() if report is None else report
        files = self.files if files is None else files
        body = json.dumps(report).encode()
        with mock.patch.object(guard, 'snapshot', return_value=files):
            return guard.check_packet(ROOT, self.fields if fields is None else fields, body,
                guard.sha(body) if digest is None else digest, archive(files) if data is None else data)

    def test_only_recognized_advisory_outcomes_pass(self):
        for reason, code in [('unsupported-inductive', 2), ('fuel-exhausted', 3), ('capacity', None)]:
            with self.subTest(reason=reason):
                report = self.fixture(reason, code)
                result = self.check(report)
                self.assertEqual(result['status'], 'pass')
                self.assertFalse(result['intake_authorized'])
                self.assertEqual(report['kernels'], [{'name': 'nanoda', 'argv': ['/synthetic/bin/nanoda_bin']}])
        self.assertEqual(self.check(self.accepted_fixture())['status'], 'pass')

    def test_capacity_can_truthfully_record_no_remaining_replay_budget(self):
        report = self.fixture('capacity', None)
        report['kernel_attempts'][0]['budget_seconds'] = 0
        self.assertEqual(self.check(report)['status'], 'pass')

    def test_unknown_failed_and_misreported_advisory_outcomes_block(self):
        changes = {
            'rejected': dict(status='rejected', reason='invalid-declaration', exit_code=1),
            'unknown': dict(status='error', reason='unrecognized-checker-result', exit_code=4),
            'invalid-axiom': dict(reason='non-standard-axiom'),
            'wrong-decline-exit': dict(exit_code=1),
            'boolean-exit': dict(exit_code=False),
            'claimed-acceptance': dict(status='accepted', reason='complete', exit_code=0),
            'invalid-budget': dict(budget_seconds=1801),
            'boolean-budget': dict(budget_seconds=True),
            'missing-detail': dict(detail=''),
            'unverified': dict(argv=['/synthetic/con-ron', '--jobs=2']),
            'relative-command': dict(argv=['con-ron', '--jobs=2', '--verified']),
            'wrong-jobs': dict(argv=['/synthetic/con-ron', '--jobs=3', '--verified']),
        }
        for name, change in changes.items():
            with self.subTest(change=name):
                report = self.fixture()
                report['kernel_attempts'][0].update(change)
                with self.assertRaises(ValueError):
                    self.check(report)

    def test_missing_duplicate_or_false_acceptance_blocks(self):
        changes = [lambda r: r.update(kernels=[]), lambda r: r.update(kernel_attempts=[]),
                   lambda r: r.update(warnings=[]),
                   lambda r: r['kernels'].append({'name': 'con-ron'}),
                   lambda r: r['kernels'].append(copy.deepcopy(r['kernels'][0])),
                   lambda r: r['kernel_attempts'].append(copy.deepcopy(r['kernel_attempts'][0]))]
        for change in changes:
            report = self.fixture()
            change(report)
            with self.subTest(change=change), self.assertRaises(ValueError):
                self.check(report)

    def test_accepted_replay_retains_strict_detail_and_provenance_gates(self):
        changes = [lambda r: r['tool_digests'].update({'con-ron': '0' * 64}),
                   lambda r: r['con_ron_checker'].update(release_tag='unreviewed'),
                   lambda r: r['kernel_attempts'][0].update(detail='con-ron: rejected: invalid declaration'),
                   lambda r: r['kernel_attempts'][0].update(detail='con-ron: accepted 123 declarations (--verified)\ncon-ron: declined: unsupported inductive X'),
                   lambda r: r['kernels'][1].update(argv=['/other/con-ron', '--jobs=2', '--verified'])]
        for change in changes:
            report = self.accepted_fixture()
            change(report)
            with self.subTest(change=change), self.assertRaises(ValueError):
                self.check(report)

    def test_source_paths_digests_trust_and_protocol_remain_bound(self):
        changes = {
            'commit': lambda r: r['source'].update(commit='0' * 40),
            'repository': lambda r: r['source'].update(repository='other/repo'),
            'project': lambda r: r['source'].update(project_path='combinatorics/other'),
            'toolchain': lambda r: r.update(lean_toolchain='leanprover/lean4:v4.0.0'),
            'status': lambda r: r.update(status='fail'),
            'stage': lambda r: r.update(stage='con-ron'),
            'errors': lambda r: r.update(errors=['failure']),
            'schema': lambda r: r.update(schema_version=1),
            'phase': lambda r: r.update(phase='preparation'),
            'profile': lambda r: r.update(execution_profile='other'),
            'trust': lambda r: r['challenge'].update(trust_level='low'),
            'dependencies': lambda r: r['challenge'].update(untrusted_sources=['other']),
            'nanoda-command': lambda r: r['kernels'][0].update(argv=['/other/nanoda_bin']),
            'protected-digest': lambda r: r.update(protected_config_sha256='0' * 64),
        }
        for name, change in changes.items():
            report = self.fixture()
            change(report)
            with self.subTest(change=name), self.assertRaises(ValueError):
                self.check(report)
        for kind in ('formalization', 'comparator', 'challenge', 'solution', 'lakefile', 'lake_manifest'):
            for key, value in [('path', PROJECT + '/other'), ('sha256', '0' * 64)]:
                report = self.fixture()
                report[kind][key] = value
                with self.subTest(kind=kind, key=key), self.assertRaises(ValueError):
                    self.check(report)
        for line in self.fixture()['comparator_log_tail'].splitlines():
            report = self.fixture()
            report['comparator_log_tail'] = report['comparator_log_tail'].replace(line, '')
            with self.subTest(missing=line), self.assertRaises(ValueError):
                self.check(report)

    def test_protected_declarations_axioms_and_commands_cannot_drift(self):
        changes = [('theorem_names', ['Other.theorem']), ('definition_names', ['Other.definition']),
                   ('permitted_axioms', ['sorryAx']), ('solution_module', 'OtherSolution'),
                   ('challenge_module', 'Challenge'),
                   ('external_kernels', {'nanoda': ['nanoda_bin']}),
                   ('external_kernels', {'nanoda': ['/synthetic/bin/nanoda_bin'], 'con-ron': ['/synthetic/con-ron']})]
        for key, value in changes:
            report = self.fixture()
            protected = json.loads(report['protected_config'])
            protected[key] = value
            report['protected_config'] = json.dumps(protected)
            report['protected_config_sha256'] = guard.sha(report['protected_config'].encode())
            with self.subTest(key=key, value=value), self.assertRaises(ValueError):
                self.check(report)

    def test_original_report_digest_and_intake_paths_remain_required(self):
        with self.assertRaisesRegex(ValueError, 'original bytes'):
            self.check(digest='0' * 64)
        for key in ('comparator_config_path', 'formalization_metadata_path'):
            fields = dict(self.fields)
            fields[key] = PROJECT + '/README.md'
            with self.subTest(key=key), self.assertRaisesRegex(ValueError, 'Wrong intake paths'):
                self.check(fields=fields)

    def test_archive_must_include_exact_source_and_nothing_else(self):
        for kind in ('metadata', 'implementation', 'missing', 'extra'):
            files = dict(self.files)
            if kind == 'metadata':
                files['formalization.yaml'] += b'\n'
            elif kind == 'implementation':
                files['DigitTransport.lean'] += b'\n'
            elif kind == 'missing':
                files.pop('README.md')
            else:
                files['not-source.txt'] = b'No unrelated or private packet contents.'
            with self.subTest(kind=kind), self.assertRaisesRegex(ValueError, 'Archive source|archive source'):
                self.check(data=archive(files))

    def test_stale_status_remains_blocked_but_explicit_future_status_is_valid(self):
        for name in ('formalization.yaml', 'README.md', 'REVIEW.md'):
            files = dict(self.files)
            files[name] += b'\nCanonical checks have not run for this source.\n'
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, 'stale blanket'):
                self.check(files=files)
        self.assertFalse(guard.status_errors({'README.md':
            b'Canonical rendering of a later source remains unperformed. Browser visual review remains pending.'}))
        self.assertTrue(guard.status_errors({'README.md':
            b'Canonical full verification and browser visual review remain unperformed for this source.'}))

    def test_other_packages_still_require_three_actual_kernel_acceptances(self):
        for project in ('topology/collectionwise-normal', 'computational-hodge/finite-periods'):
            report = self.fixture()
            fields = dict(self.fields)
            fields.update(project_path=project, comparator_config_path=project + '/comparator.json',
                          formalization_metadata_path=project + '/formalization.yaml')
            report['source']['project_path'] = project
            for kind in ('formalization', 'comparator', 'challenge', 'solution', 'lakefile', 'lake_manifest'):
                report[kind]['path'] = report[kind]['path'].replace(PROJECT, project)
            with self.subTest(project=project), self.assertRaisesRegex(ValueError, 'independent kernel'):
                guard.bind_full(report, fields, self.files)


if __name__ == '__main__':
    unittest.main()
