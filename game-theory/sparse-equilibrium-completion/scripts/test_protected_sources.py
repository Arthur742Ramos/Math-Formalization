#!/usr/bin/env python3
"""Pure source/isolation regressions; never invokes Lean or Lake."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from protected_sources import (MODULES, aggregate, checked_graph, header_imports,
                               require_clean_output_tree, transform, validate)

if not __debug__ or sys.flags.optimize or 'PYTHONOPTIMIZE' in os.environ:
    raise SystemExit('Protected regression controls refuse optimized Python')


class ProtectedSourceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(__file__).resolve().parents[1]
        cls.temp = tempfile.TemporaryDirectory(prefix='protected-source-tests-')
        cls.fixture = Path(cls.temp.name)/'package'
        cls.fixture.mkdir()
        (cls.fixture/'verification').mkdir()
        (cls.fixture/'scripts').mkdir()
        shutil.copyfile(cls.root/'comparator.json', cls.fixture/'comparator.json')
        shutil.copyfile(cls.root/'lakefile.toml', cls.fixture/'lakefile.toml')
        shutil.copyfile(cls.root/'scripts/CompareExports.lean', cls.fixture/'scripts/CompareExports.lean')
        shutil.copyfile(cls.root/'verification/protected-canonical-sources.json',
                        cls.fixture/'verification/protected-canonical-sources.json')
        for name in MODULES:
            shutil.copyfile(cls.root/(name+'.lean'), cls.fixture/(name+'.lean'))
        shutil.copytree(cls.root/'ProtectedSources', cls.fixture/'ProtectedSources')
        shutil.copyfile(cls.root/'SECChallenge.lean', cls.fixture/'SECChallenge.lean')

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def mutate_rejected(self, path, content):
        original = path.read_bytes()
        try:
            path.write_bytes(content)
            with self.assertRaises(ValueError):
                validate(self.fixture)
        finally:
            path.write_bytes(original)

    def test_01_exact_bijection(self):
        result = validate(self.fixture)
        self.assertEqual(result['protected_copies'], 373)
        self.assertEqual(set(result['protected_build_order']), {'ProtectedSources.'+n for n in MODULES})

    def test_02_only_exact_import_tokens_change(self):
        source = b'/-- import SparseCompletion -/\nmodule\npublic meta import all SparseCompletion Mathlib.Tactic -- x\n\npublic section\ndef text := "import SparseCompletion"\n'
        self.assertEqual(transform(source), source.replace(b'import all SparseCompletion ', b'import all ProtectedSources.SparseCompletion '))
        self.assertEqual(len(header_imports(source)), 2)

    def test_03_changed_body(self):
        p = self.fixture/'ProtectedSources/SparseCompletion.lean'
        self.mutate_rejected(p, p.read_bytes()+b'\nexample : True := True.intro\n')

    def test_04_missing_copy(self):
        p = self.fixture/'ProtectedSources/SparseCompletion.lean'
        original = p.read_bytes()
        try:
            p.unlink()
            with self.assertRaises(ValueError): validate(self.fixture)
        finally:
            p.write_bytes(original)

    def test_05_misdirected_import(self):
        p = self.fixture/'ProtectedSources/MomentCompression.lean'
        self.mutate_rejected(p, p.read_bytes().replace(b'ProtectedSources.SparseCompletion', b'ProtectedSources.GameModel'))

    def test_06_original_import_leakage(self):
        p = self.fixture/'ProtectedSources/MomentCompression.lean'
        self.mutate_rejected(p, p.read_bytes().replace(b'ProtectedSources.SparseCompletion', b'SparseCompletion'))

    def test_07_changed_canonical_and_copy_together(self):
        p = self.fixture/'SparseCompletion.lean'
        self.mutate_rejected(p, p.read_bytes()+b'\n-- drift must not become a new protected baseline\n')

    def test_08_stale_artifact_and_unexpected_copy(self):
        for suffix in ('.olean', '.lean'):
            p = self.fixture/'ProtectedSources'/('Unexpected'+suffix)
            try:
                p.write_bytes(b'stale')
                with self.assertRaises(ValueError): validate(self.fixture)
            finally:
                p.unlink()

    def test_09_stale_output_tree(self):
        p = Path(self.temp.name)/'stale-output'
        p.mkdir()
        (p/'Challenge.olean').write_bytes(b'stale')
        with self.assertRaises(ValueError): require_clean_output_tree(p)
        require_clean_output_tree(Path(self.temp.name)/'fresh-output')

    def test_10_aggregator_leakage(self):
        self.mutate_rejected(self.fixture/'SECChallenge.lean', aggregate()+b'public import SECSolution\n')

    def test_11_cycle_and_unsupported_import(self):
        with self.assertRaises(ValueError):
            checked_graph({'A': b'import B\n', 'B': b'import A\n'})
        with self.assertRaises(ValueError):
            header_imports(b'module\nprivate import SparseCompletion\n')

    def test_12_optimized_refusal(self):
        result = subprocess.run([sys.executable, '-O', str(self.root/'scripts/protected_sources.py')],
                                cwd=self.temp.name, capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('refuse optimized Python', result.stderr)

    def test_13_library_glob_selects_exact_submodules(self):
        result = validate(self.fixture)['protected_library']
        self.assertEqual(result['globs'], ['ProtectedSources.+'])
        self.assertEqual(result['matched_modules'], ['ProtectedSources.'+n for n in MODULES])
        self.assertEqual(len(result['matched_modules']), 373)
        self.assertNotIn('ProtectedSources', result['matched_modules'])
        self.assertFalse(result['root_module_present'])
        config = self.fixture/'lakefile.toml'
        original = config.read_bytes()
        for suffix in (b'*', b'**'):
            self.mutate_rejected(config, original.replace(b'ProtectedSources.+', b'ProtectedSources.'+suffix))
        self.mutate_rejected(config, original.replace(b'name = "ProtectedSources"', b'name = "MissingProtectedLibrary"'))
        root_module = self.fixture/'ProtectedSources.lean'
        try:
            root_module.write_text('module\n')
            with self.assertRaises(ValueError): validate(self.fixture)
        finally:
            root_module.unlink()


if __name__ == '__main__':
    unittest.main()
