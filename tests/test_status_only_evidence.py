import copy
import json
import pathlib
import sys
import tempfile
import unittest
from unittest import mock

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from check_status_only_evidence import classify
import check_status_only_evidence as reuse


class StatusOnlyEvidence(unittest.TestCase):
    def setUp(self):
        metadata = {'project': {'authors': ['A'], 'license': 'Apache-2.0'},
                    'status': {'known_gaps': 'old', 'sorry_count': 0},
                    'review': {'notes': 'old', 'status': 'agent-reviewed'}}
        self.old = {'README.md': b'old', 'formalization.yaml': json.dumps(metadata).encode(),
                    'Proof.lean': b'theorem proof', 'comparator.json': b'{}',
                    'lean-toolchain': b'lean', 'lake-manifest.json': b'{}'}
        self.new = copy.deepcopy(self.old)
        metadata['status']['known_gaps'] = 'dated new status'
        self.new['formalization.yaml'] = json.dumps(metadata).encode()
        self.new['README.md'] = b'dated new status'
        self.modes = {key: '100644' for key in self.old}

    def check(self):
        return classify(self.old, self.new, self.modes, self.modes)

    def test_status_only_passes(self):
        self.assertEqual(self.check(), ['README.md', 'formalization.yaml'])

    def test_proof_comparator_toolchain_and_lock_changes_fail(self):
        for name in ['Proof.lean', 'comparator.json', 'lean-toolchain', 'lake-manifest.json']:
            with self.subTest(name=name):
                original = self.new[name]
                self.new[name] = original + b'changed'
                with self.assertRaises(ValueError): self.check()
                self.new[name] = original

    def test_attribution_or_mathematical_status_change_fails(self):
        for section, key, value in [('project', 'authors', ['B']), ('status', 'sorry_count', 1),
                                    ('review', 'status', 'human-reviewed')]:
            with self.subTest(section=section, key=key):
                previous = self.new['formalization.yaml']
                value_map = json.loads(previous)
                value_map[section][key] = value
                self.new['formalization.yaml'] = json.dumps(value_map).encode()
                with self.assertRaises(ValueError): self.check()
                self.new['formalization.yaml'] = previous


class EvidenceChain(unittest.TestCase):
    def setUp(self):
        self.old_commit, self.new_commit = 'a'*40, 'b'*40
        self.project, self.pipeline = 'topology/example', 'c'*40
        self.full_sha, self.render_sha, self.fa_sha, self.ra_sha, self.review_sha, self.fr_sha, self.scope_sha = [x*64 for x in '1234567']
        self.repo = 'Arthur742Ramos/Math-Formalization'
        meta = {'project': {'authors': ['A']}, 'status': {'known_gaps': 'old', 'sorry_count': 0}, 'review': {'notes': 'old'}}
        config = {'challenge_module': 'Challenge', 'solution_module': 'Solution', 'theorem_names': ['t'], 'definition_names': []}
        self.old = {'README.md': b'old', 'formalization.yaml': json.dumps(meta).encode(), 'comparator.json': json.dumps(config).encode(), 'Challenge.lean': b'theorem', 'Solution.lean': b'proof', 'lakefile.toml': b'', 'lean-toolchain': b'lean'}
        self.new = dict(self.old, **{'README.md': b'new'})
        self.modes = {name: '100644' for name in self.old}
        self.fields = {'repository': self.repo, 'project_path': self.project, 'commit': self.new_commit, 'comparator_config_path': self.project+'/comparator.json', 'formalization_metadata_path': self.project+'/formalization.yaml'}
        source = {'repository': self.repo, 'project_path': self.project, 'commit': self.old_commit, 'challenge_path': self.project+'/Challenge.lean', 'solution_path': self.project+'/Solution.lean', 'comparator_config_path': self.project+'/comparator.json', 'lakefile_path': self.project+'/lakefile.toml', 'lean_toolchain_path': self.project+'/lean-toolchain', 'challenge_sha256': reuse.sha(b'theorem')}
        self.full = {'source': {'commit': self.old_commit}}
        self.render = {'status': 'pass', 'stage': 'complete', 'errors': [], 'source': source, 'renderer_commit': self.pipeline, 'format': 'verso-html', 'entrypoint': 'Challenge/index.html', 'lean_toolchain': 'lean', 'surface': {'declarations': ['t']}}
        def adapter(mode, report, phases):
            return {'status': 'pass', 'mode': mode, 'repository': self.repo, 'commit': self.old_commit, 'pipeline_commit': self.pipeline, 'report_sha256': report, 'bwrap_sha256': '8'*64, 'inputs_sha256': '9'*64, 'steps': [{'exit_code': 0, 'argv': (['python', '/p/verify_submission.py', phase] if mode == 'full' else ['python', '-m', 'scripts.render_challenge', phase])} for phase in phases]}
        self.fa = adapter('full', self.full_sha, ['prepare', 'check-capacity', 'execute'])
        self.ra = adapter('render', self.render_sha, ['prepare', 'execute'])
        self.review = {'status': 'pass_final_independent_release_review', 'source_commit': self.old_commit, 'full_report_sha256': self.full_sha, 'render_report_sha256': self.render_sha, 'render_receipt_sha256': self.ra_sha, 'pipeline_commit': self.pipeline, 'independent_full_review_sha256': self.fr_sha, 'package_tree': 'oldpkg'}
        self.fr = {'status': 'pass_full_report_authentication', 'source_commit': self.old_commit, 'pipeline_commit': self.pipeline, 'package_tree': 'oldpkg', 'report_sha256': self.full_sha, 'receipt_sha256': self.fa_sha}
        self.scope = {'status': 'pass', 'kind': 'independent-source-boundary-review', 'historical_commit': self.old_commit, 'corrected_commit': self.new_commit, 'historical_package_tree': 'oldpkg', 'corrected_package_tree': 'newpkg', 'historical_repository_tree': 'oldroot', 'corrected_repository_tree': 'newroot', 'repository_diff_sha256': reuse.sha(b'diff'), 'pipeline_commit': self.pipeline, 'historical_full_report_sha256': self.full_sha, 'historical_render_report_sha256': self.render_sha, 'historical_bwrap_sha256': '8'*64, 'historical_full_inputs_sha256': '9'*64, 'historical_render_inputs_sha256': '9'*64, 'selected_proof_inputs': 'byte-identical', 'whole_checkout_verification': 'not-run', 'render_impact_reviewed': True, 'claims_match_evidence': True, 'attribution_accurate': True, 'unresolved_blockers': [], 'reviewer': 'independent reviewer', 'findings': ['reviewed repository projection']}
        self.objects = {'full': self.full, 'render': self.render, 'fa': self.fa, 'ra': self.ra, 'review': self.review, 'fr': self.fr, 'scope': self.scope}

    def check(self):
        return classify(self.old, self.new, self.modes, self.modes)

    def run_check(self):
        def git_output(argv, **kwargs):
            target = argv[-1]
            if target.endswith('^{tree}'): return 'oldroot' if target.startswith(self.old_commit) else 'newroot'
            if ':' in target: return 'oldpkg' if target.startswith(self.old_commit) else 'newpkg'
            return b'diff'
        def binder(report, fields, files):
            if report['source']['commit'] != fields['commit']: raise ValueError('wrong full source')
        with tempfile.TemporaryDirectory() as directory:
            archive = pathlib.Path(directory)/'archive.tar'; archive.write_bytes(b'archive')
            with mock.patch.object(reuse, 'snapshot', side_effect=lambda root, commit, project: self.old if commit == self.old_commit else self.new), mock.patch.object(reuse, 'modes', return_value=self.modes), mock.patch.object(reuse, 'check_status'), mock.patch.object(reuse, 'check_archive'), mock.patch.object(reuse, 'bind_full', side_effect=binder), mock.patch.object(reuse, '_read_authenticated', side_effect=lambda path, expected, label: self.objects[path]), mock.patch.object(reuse.subprocess, 'check_output', side_effect=git_output):
                return reuse.check(pathlib.Path(directory), {'proposed_submission_fields': self.fields, 'pipeline_commit': self.pipeline}, archive, self.old_commit, 'full', self.full_sha, 'fa', self.fa_sha, 'render', self.render_sha, 'ra', self.ra_sha, 'review', self.review_sha, 'fr', self.fr_sha, 'scope', self.scope_sha)

    def test_bound_history_is_not_relabelled_fresh(self):
        result = self.run_check()
        self.assertEqual(result['status'], 'conditional-pass')
        self.assertEqual(result['current_source_full'], 'not run')
        self.assertEqual(result['current_source_render'], 'not run')

    def test_wrong_sources_phases_and_review_rejected(self):
        mutations = [(self.full['source'], 'commit', self.new_commit), (self.fa, 'repository', 'other'), (self.fa['steps'][1], 'exit_code', 1), (self.ra['steps'][0], 'argv', ['python','-m','scripts.render_challenge','execute']), (self.review, 'pipeline_commit', 'd'*40), (self.fr, 'receipt_sha256', '0'*64)]
        for obj, key, wrong in mutations:
            with self.subTest(key=key):
                before = obj[key]; obj[key] = wrong
                with self.assertRaises(ValueError): self.run_check()
                obj[key] = before

    def test_unreviewed_claims_or_repository_boundary_rejected(self):
        for key, wrong in [('selected_proof_inputs','unknown'), ('whole_checkout_verification','pass'), ('claims_match_evidence',False), ('attribution_accurate',False), ('render_impact_reviewed',False), ('unresolved_blockers',['unresolved']), ('repository_diff_sha256','0'*64)]:
            with self.subTest(key=key):
                before = self.scope[key]; self.scope[key] = wrong
                with self.assertRaises(ValueError): self.run_check()
                self.scope[key] = before

    def test_new_or_removed_file_fails(self):
        self.new['Secret.lean'] = b'x'
        with self.assertRaises(ValueError): self.check()

    def test_mode_change_or_symlink_fails(self):
        modes = dict(self.modes, **{'Challenge.lean': '100755'})
        with self.assertRaises(ValueError): classify(self.old, self.new, self.modes, modes)
        modes = dict(self.modes, **{'Challenge.lean': '120000'})
        with self.assertRaises(ValueError): classify(self.old, self.new, modes, modes)

    def test_duplicate_metadata_key_fails(self):
        self.new['formalization.yaml'] = b'{"status":{"known_gaps":"one","known_gaps":"two"},"review":{"notes":"x"}}'
        with self.assertRaises(ValueError): self.check()

    def test_invalid_or_non_string_status_fails(self):
        metadata = json.loads(self.new['formalization.yaml'])
        metadata['review']['notes'] = False
        self.new['formalization.yaml'] = json.dumps(metadata).encode()
        with self.assertRaises(ValueError): self.check()

    def test_bool_integer_float_and_nonfinite_are_not_equal(self):
        self.assertEqual(0, False)  # Demonstrates why raw Python object equality is insufficient.
        self.assertEqual(0, 0.0)
        for value in [False, 0.0, float('nan'), float('inf')]:
            with self.subTest(value=value):
                previous = self.new['formalization.yaml']
                metadata = json.loads(previous)
                metadata['status']['sorry_count'] = value
                self.new['formalization.yaml'] = json.dumps(metadata).encode()
                with self.assertRaises(ValueError): self.check()
                self.new['formalization.yaml'] = previous


if __name__ == '__main__':
    unittest.main()
