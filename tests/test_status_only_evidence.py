import copy
import json
import pathlib
import sys
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from check_status_only_evidence import classify


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

    def test_new_or_removed_file_fails(self):
        self.new['Secret.lean'] = b'x'
        with self.assertRaises(ValueError): self.check()

    def test_mode_change_or_symlink_fails(self):
        modes = dict(self.modes, **{'Proof.lean': '100755'})
        with self.assertRaises(ValueError): classify(self.old, self.new, self.modes, modes)
        modes = dict(self.modes, **{'Proof.lean': '120000'})
        with self.assertRaises(ValueError): classify(self.old, self.new, modes, modes)

    def test_duplicate_metadata_key_fails(self):
        self.new['formalization.yaml'] = b'{"status":{"known_gaps":"one","known_gaps":"two"},"review":{"notes":"x"}}'
        with self.assertRaises(ValueError): self.check()

    def test_invalid_or_non_string_status_fails(self):
        metadata = json.loads(self.new['formalization.yaml'])
        metadata['review']['notes'] = False
        self.new['formalization.yaml'] = json.dumps(metadata).encode()
        with self.assertRaises(ValueError): self.check()


if __name__ == '__main__':
    unittest.main()
