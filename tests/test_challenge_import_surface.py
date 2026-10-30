import importlib.util
import tempfile
import unittest
from pathlib import Path

spec = importlib.util.spec_from_file_location(
    'challenge_import_surface', Path(__file__).resolve().parents[1] / 'scripts/check_challenge_import_surface.py')
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)


def header(*modules):
    return {'imports': [{'errors': [], 'result': {'isModule': True,
            'imports': [{'module': name} for name in modules]}}]}


class DirectImportSurfaceTests(unittest.TestCase):
    def test_local_proof_module_is_flagged(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'Mycielski').mkdir()
            (root / 'Mycielski/Independent.lean').write_text('module\n')
            self.assertEqual(mod.project_local_imports(header('Init', 'Mathlib.Tactic',
                                                              'Mycielski.Independent'), root),
                             ['Mycielski.Independent'])

    def test_clean_header_and_duplicate_imports(self):
        with tempfile.TemporaryDirectory() as tmp:
            self.assertEqual(mod.project_local_imports(header('Init', 'Init', 'Mathlib.Tactic'), tmp), [])

    def test_project_shadow_of_trusted_namespace_is_flagged(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'Mathlib').mkdir()
            (root / 'Mathlib/Tactic.lean').write_text('module\n')
            self.assertEqual(mod.project_local_imports(header('Mathlib.Tactic'), root), ['Mathlib.Tactic'])

    def test_unknown_or_invalid_header_fails_closed(self):
        with tempfile.TemporaryDirectory() as tmp:
            for bad in ({}, {'imports': []}, {'imports': [{'errors': ['error']}]},
                        header('../local'), {'imports': [{'errors': [], 'result':
                                                        {'isModule': False, 'imports': []}}]}):
                with self.subTest(bad=bad), self.assertRaises(ValueError):
                    mod.project_local_imports(bad, tmp)

    def test_nondefault_source_root_is_checked_when_supplied(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'src/Foo').mkdir(parents=True)
            (root / 'src/Foo/Bar.lean').write_text('module\n')
            self.assertEqual(mod.project_local_imports(header('Foo.Bar'), root, ['src']), ['Foo.Bar'])
            with self.assertRaises(FileNotFoundError):
                mod.project_local_imports(header('Foo.Bar'), root, ['missing'])

    def test_dangling_and_escaping_symlinks_fail_closed(self):
        with tempfile.TemporaryDirectory() as tmp, tempfile.TemporaryDirectory() as outside:
            root = Path(tmp)
            (root / 'Local').mkdir()
            link = root / 'Local/Proof.lean'
            try:
                link.symlink_to(root / 'missing.lean')
            except (OSError, NotImplementedError):
                self.skipTest('symlink creation is unavailable on this host')
            with self.assertRaises(ValueError):
                mod.project_local_imports(header('Local.Proof'), root)
            link.unlink()
            (Path(outside) / 'Proof.lean').write_text('module\n')
            link.symlink_to(Path(outside) / 'Proof.lean')
            with self.assertRaises(ValueError):
                mod.project_local_imports(header('Local.Proof'), root)
            with self.assertRaises(ValueError):
                mod.project_local_imports(header('Local.Proof'), root, [outside])

if __name__ == '__main__':
    unittest.main()

