#!/usr/bin/env python3
"""Synthetic filesystem fixtures for runtime-root/facet input envelopes."""
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch
from protected_sources import FACETS
from verification_inputs import capture

if not __debug__ or sys.flags.optimize or 'PYTHONOPTIMIZE' in os.environ:
    raise SystemExit('Input regression controls refuse optimized Python')


class InputEnvelopeTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='input-envelope-tests-')
        self.root = Path(self.temp.name)/'package'
        self.prefix = Path(self.temp.name)/'compiler'
        self.root.mkdir(); self.prefix.mkdir()
        packages = [{'name': 'dep'+str(i), 'rev': str(i)*40} for i in range(9)]
        (self.root/'lake-manifest.json').write_text(json.dumps({'packages': packages}))
        for item in packages:
            (self.root/'.lake/packages'/item['name']).mkdir(parents=True)
        self.own = self.root/'Own.lean'
        self.own.write_text('module\npublic section\ndef own := 1\n')
        for name, imports in [('Init', ''), ('Lean', 'public import Lean.RuntimeOnly\n'),
                              ('Lean.RuntimeOnly', ''), ('Lake', 'public import Lake.RuntimeOnly\n'),
                              ('Lake.RuntimeOnly', '')]:
            source_root = self.prefix/('src/lean/lake' if name.startswith('Lake') else 'src/lean')
            source = source_root/Path(name.replace('.', '/')+'.lean')
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text('module\n'+imports+'public section\n')
            for suffix in FACETS:
                target = self.prefix/'lib/lean'/Path(name.replace('.', '/')+suffix)
                target.parent.mkdir(parents=True, exist_ok=True); target.write_bytes(b'fixture-'+name.encode())
        self.git = patch('verification_inputs.git_states', return_value=[{'fixture': 'nine states are mocked; no git subprocess'}])
        self.git.start()

    def tearDown(self):
        self.git.stop(); self.temp.cleanup()

    def envelope(self):
        return capture(self.root, self.prefix, [self.own], [self.root/'lake-manifest.json'])

    def external_module(self, dependency, name, contents):
        source_root = self.root/'.lake/packages'/dependency
        relative = Path(name.replace('.', '/'))
        source = source_root/relative.with_suffix('.lean')
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_text('module\npublic section\n')
        for suffix in FACETS:
            target = source_root/'.lake/build/lib/lean'/Path(str(relative)+suffix)
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(contents)

    def import_external(self, name):
        self.own.write_text('module\npublic import '+name+'\npublic section\ndef own := 1\n')

    def test_first_package_directory_refuses_missing_module_despite_later_copy(self):
        first = self.root/'.lake/packages/dep0/.lake/build/lib/lean/Fixture'
        first.mkdir(parents=True)
        self.external_module('dep1', 'Fixture.Child', b'later complete module')
        self.import_external('Fixture.Child')
        with self.assertRaisesRegex(ValueError, 'Module missing from first selected package root'):
            self.envelope()

    def test_first_package_olean_refuses_missing_child_despite_later_copy(self):
        first = self.root/'.lake/packages/dep0/.lake/build/lib/lean/Fixture.olean'
        first.parent.mkdir(parents=True)
        first.write_bytes(b'package root without child directory')
        self.external_module('dep1', 'Fixture.Child', b'later complete module')
        self.import_external('Fixture.Child')
        with self.assertRaisesRegex(ValueError, 'Module missing from first selected package root'):
            self.envelope()

    def test_first_complete_package_selected_over_distinct_later_copy(self):
        self.external_module('dep0', 'Fixture.Child', b'first complete module')
        self.external_module('dep1', 'Fixture.Child', b'later different module')
        self.import_external('Fixture.Child')
        row = self.envelope()['resolved_modules']['Fixture.Child']
        self.assertEqual(row['artifact_root'],
                         str(self.root/'.lake/packages/dep0/.lake/build/lib/lean'))
        self.assertTrue(all('/dep0/' in facet['path'] for facet in row['facets']))

    def test_unshadowed_later_package_selected(self):
        self.external_module('dep1', 'Fixture.Child', b'unshadowed later module')
        self.import_external('Fixture.Child')
        row = self.envelope()['resolved_modules']['Fixture.Child']
        self.assertEqual(row['artifact_root'],
                         str(self.root/'.lake/packages/dep1/.lake/build/lib/lean'))

    def test_runtime_roots_even_without_target_imports(self):
        result = self.envelope()
        self.assertEqual(result['runtime_roots'], ['Init', 'Lean', 'Lake'])
        self.assertEqual(set(result['resolved_modules']),
                         {'Own', 'Init', 'Lean', 'Lean.RuntimeOnly', 'Lake', 'Lake.RuntimeOnly'})
        self.assertIn('/src/lean/lake/', result['resolved_modules']['Lake']['source']['path'])
        self.assertEqual(sum(len(row.get('facets', [])) for row in result['resolved_modules'].values()), 25)

    def test_missing_runtime_facet_refused(self):
        (self.prefix/'lib/lean/Lean/RuntimeOnly.ir.sig').unlink()
        with self.assertRaises(ValueError): self.envelope()

    def test_missing_paired_lake_source_refused(self):
        (self.prefix/'src/lean/lake/Lake.lean').unlink()
        with self.assertRaises(ValueError): self.envelope()

    def test_changed_cached_runtime_bytes_detected(self):
        before = self.envelope()
        (self.prefix/'lib/lean/Lake/RuntimeOnly.ir').write_bytes(b'changed')
        self.assertNotEqual(before, self.envelope())

    def test_upstream_to_project_import_refused(self):
        (self.prefix/'src/lean/Lean/RuntimeOnly.lean').write_text('module\npublic import Own\n')
        with self.assertRaises(ValueError): self.envelope()

    def test_runtime_shared_objects_bound(self):
        shared = self.root/'.lake/packages/dep0/.lake/build/lib/libFixture.so'
        shared.parent.mkdir(parents=True)
        shared.write_bytes(b'fixture shared library; never loaded')
        before = self.envelope()
        self.assertIn(str(shared), before['files'])
        shared.write_bytes(b'changed')
        self.assertNotEqual(before, self.envelope())


if __name__ == '__main__':
    unittest.main()
