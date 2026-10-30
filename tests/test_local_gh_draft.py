"""Local draft catalog guards must not imply publication or weaken public checks."""
import copy
import hashlib
import pathlib
import sys
import tempfile
import unittest
from unittest import mock

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import check_preparations as prep
import check_gh_local_draft as package_check


class LocalDraftReferences(unittest.TestCase):
    def setUp(self):
        self.commit = 'a' * 40
        self.p = {'name': 'Example', 'scope': 'Example scope', 'path': 'topology/gottschalk-hedlund',
                  'state': 'local-development-draft', 'publication_status': 'local-only',
                  'registry_public_status': 'unconfirmed', 'catalog_checkpoint': '2026-10-30',
                  'source_snapshot': {'commit': self.commit, 'tree': 'b' * 40}}
        self.row = '| Example | Example scope | Local draft; intake unconfirmed | Local commit `' + self.commit + '` |'

    def test_local_row_is_explicitly_local(self):
        prep.check_preparation_source_reference(self.p, self.row, 'Arthur742Ramos/Math-Formalization')
        for key, value in [('publication_status', 'public'), ('registry_public_status', 'absent'),
                           ('path', 'topology/another'), ('catalog_checkpoint', 'today')]:
            changed = dict(self.p, **{key: value})
            with self.subTest(key=key), self.assertRaises(AssertionError):
                prep.check_preparation_source_reference(changed, self.row, 'Arthur742Ramos/Math-Formalization')
        for row in [self.row.replace(self.commit, 'c' * 40), self.row.replace('intake unconfirmed', 'not submitted'),
                    self.row + ' https://github.com/a/b', self.row + ' PALOMAR-2026-10-30-000001']:
            with self.subTest(row=row), self.assertRaises(AssertionError):
                prep.check_preparation_source_reference(self.p, row, 'Arthur742Ramos/Math-Formalization')

    def test_other_states_still_require_exact_public_link(self):
        p = dict(self.p, state='reviewed-preparation-not-submitted')
        with self.assertRaises(AssertionError):
            prep.check_preparation_source_reference(p, self.row, 'Arthur742Ramos/Math-Formalization')
        url = 'https://github.com/Arthur742Ramos/Math-Formalization/tree/' + self.commit + '/' + p['path']
        prep.check_preparation_source_reference(p, url, 'Arthur742Ramos/Math-Formalization')
        with self.assertRaises(AssertionError):
            prep.check_preparation_source_reference(p, url.replace(self.commit, 'c' * 40), 'Arthur742Ramos/Math-Formalization')


class LocalDraftFileBinding(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='gh-local-catalog-test-')
        self.addCleanup(self.tmp.cleanup)
        self.pkg = pathlib.Path(self.tmp.name) / 'package'
        (self.pkg / 'nested').mkdir(parents=True)
        self.files = {'top.txt': b'top\n', 'nested/item.txt': b'nested\n'}
        for name, data in self.files.items():
            (self.pkg / name).write_bytes(data)
        digests = {n: hashlib.sha256(b).hexdigest() for n, b in self.files.items()}
        self.p = {'path': 'topology/gottschalk-hedlund',
                  'source_files_sha256': {'top.txt': digests['top.txt']},
                  'nested_source_files_sha256': {'nested/item.txt': digests['nested/item.txt']}}
        self.tree = dict(self.files)
        self.mode = '100644'

    def call(self):
        def fake(argv, **kwargs):
            if 'ls-tree' in argv:
                return b''.join((self.mode + ' blob ' + 'a' * 40 + '\t' + self.p['path'] + '/' + n + '\0').encode() for n in self.tree)
            if 'show' in argv:
                name = argv[-1].split(':' + self.p['path'] + '/', 1)[1]
                return self.tree[name]
            raise AssertionError(argv)
        with mock.patch.object(prep.subprocess, 'check_output', side_effect=fake):
            prep.check_local_draft_files(self.p, 'a' * 40, self.pkg)

    def test_all_files_are_bound_to_source_and_worktree(self):
        self.call()
        (self.pkg / 'nested/item.txt').write_bytes(b'changed')
        with self.assertRaises(AssertionError): self.call()

    def test_rejects_extra_missing_unsafe_and_nonregular_sources(self):
        self.tree['extra'] = b'extra'
        with self.assertRaises(AssertionError): self.call()
        del self.tree['extra']; self.mode = '120000'
        with self.assertRaises(AssertionError): self.call()
        self.mode = '100644'; del self.tree['nested/item.txt']
        with self.assertRaises(AssertionError): self.call()
        self.tree['nested/item.txt'] = self.files['nested/item.txt']
        self.p['nested_source_files_sha256']['../escape'] = 'a' * 64
        with self.assertRaises(AssertionError): self.call()

    def test_rejects_mismatching_git_blob(self):
        self.tree['top.txt'] = b'changed in git'
        with self.assertRaises(AssertionError): self.call()


class ImportClosure(unittest.TestCase):
    def test_challenge_header_rejects_inline_comment_imports(self):
        package_check.check_challenge_header(package_check.CHALLENGE_HEADER)
        for line in ['/- comment -/ public import Mycielski', 'public /- comment -/ import Mycielski',
                     'meta import Mycielski', 'public import all Mycielski']:
            changed = package_check.CHALLENGE_HEADER.replace('module\n', 'module\n' + line + '\n', 1)
            with self.subTest(line=line), self.assertRaises(AssertionError):
                package_check.check_challenge_header(changed)

    def test_exact_public_imports_only(self):
        self.assertEqual(package_check.imports('public import Mathlib.Tactic\n'), ['Mathlib.Tactic'])
        for line in ['import Mathlib.Tactic', 'meta import Mycielski', 'public meta import Mycielski',
                     'public import all Mycielski', 'public import Mathlib.Tactic -- trailing',
                     'public import Mathlib.Tactic Mycielski']:
            with self.subTest(line=line), self.assertRaises(AssertionError):
                package_check.imports(line + '\n')


if __name__ == '__main__':
    unittest.main()
