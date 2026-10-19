"""Missing or misleading material-predicate evidence must fail before intake."""
import copy
import json
import pathlib
import shutil
import sys
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from check_imported_definitions import check, sha


class ImportedDefinitionEvidence(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.project = pathlib.Path(self.temp.name) / 'project'
        shutil.copytree(ROOT / 'topology/kuratowski-ulam', self.project,
                        ignore=shutil.ignore_patterns('.lake', '__pycache__'))
        self.file = self.project / 'verification/material-imported-definitions.json'
        self.data = json.loads(self.file.read_text())

    def write(self):
        self.file.write_text(json.dumps(self.data, ensure_ascii=False))

    def reject(self):
        self.write()
        with self.assertRaises((ValueError, KeyError)):
            check(self.project)

    def test_retained_evidence_passes_with_scope_limit(self):
        result = check(self.project)
        self.assertEqual(result['upstream_origin'], 'not-checked')
        self.assertEqual(result['upstream_files_authenticated'], 0)

    def test_missing_manifest_rejected(self):
        self.file.unlink()
        with self.assertRaises(ValueError):
            check(self.project)

    def test_empty_inventory_rejected(self):
        self.data['required_declarations'] = []
        self.reject()

    def test_omitted_material_definition_rejected(self):
        self.data['material_declarations'] = []
        self.reject()

    def test_duplicate_definition_rejected(self):
        self.data['material_declarations'] *= 2
        self.reject()

    def test_wrong_dependency_pin_rejected(self):
        self.data['dependency']['commit'] = '0' * 40
        self.reject()

    def test_moving_source_url_rejected(self):
        self.data['source_files'][0]['url'] = self.data['source_files'][0]['url'].replace(
            self.data['dependency']['commit'], 'main')
        self.reject()

    def test_forged_excerpt_rejected(self):
        self.data['source_files'][0]['excerpts'][1]['text'] += '-- invented\n'
        self.reject()

    def test_wrong_line_range_rejected(self):
        self.data['source_files'][0]['excerpts'][1]['last_line'] += 1
        self.reject()

    def test_missing_selected_usage_rejected(self):
        self.data['material_declarations'][0]['used_by'] = []
        self.reject()

    def test_foreign_selected_usage_rejected(self):
        self.data['material_declarations'][0]['used_by'] = ['Other.theorem']
        self.reject()

    def test_equivalence_misrepresented_as_rfl_rejected(self):
        self.data['material_declarations'][0]['bridge_kind'] = 'definitional-equality'
        self.reject()

    def test_unsafe_bridge_path_rejected(self):
        self.data['checked_bridge_modules'][0]['path'] = '../ChallengeTests.lean'
        self.reject()

    def test_stale_bridge_hash_rejected(self):
        (self.project / 'ChallengeTests.lean').write_text('module\n')
        self.reject()

    def test_unbuilt_bridge_rejected(self):
        self.data['checked_bridge_modules'][0]['module'] = 'Unused'
        self.data['checked_bridge_modules'][0]['path'] = 'Unused.lean'
        self.reject()

    def test_symlink_documentation_rejected(self):
        doc = self.project / self.data['documentation']
        doc.unlink()
        doc.symlink_to(ROOT / 'topology/kuratowski-ulam/MATERIAL-DEFINITIONS.md')
        self.reject()


if __name__ == '__main__':
    unittest.main()
