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
    PACKAGE = 'topology/kuratowski-ulam'

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.project = pathlib.Path(self.temp.name) / 'project'
        shutil.copytree(ROOT / self.PACKAGE, self.project,
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


class ClassAndLiteralEvidence(ImportedDefinitionEvidence):
    PACKAGE = 'topology/locally-compact-baire'

    def test_class_fields_cannot_be_labelled_literal_unfolding(self):
        self.data['material_declarations'][0]['bridge_kind'] = 'literal-unfolding'
        self.reject()

    def test_class_cannot_be_labelled_definition(self):
        self.data['material_declarations'][0]['declaration_kind'] = 'def'
        self.reject()

    def test_unrecognized_schema_rejected(self):
        self.data['schema_version'] = 99
        self.reject()

    def test_v2_cannot_downgrade_class_to_legacy_schema(self):
        self.data['schema_version'] = 1
        self.reject()

    def test_missing_dependency_expansion_rejected(self):
        self.data['material_declarations'][0]['dependency_expansion'] = ''
        self.reject()

    def test_missing_proof_status_rejected(self):
        self.data['material_declarations'][0]['proof_status'] = ''
        self.reject()

    def test_missing_semantic_bridge_reference_rejected(self):
        self.data['material_declarations'][0]['bridge_excerpts'] = []
        self.reject()

    def test_foreign_semantic_bridge_reference_rejected(self):
        self.data['material_declarations'][0]['bridge_excerpts'] = ['invented']
        self.reject()

    def test_wrong_structure_kind_rejected(self):
        self.data['material_declarations'][0]['declaration_kind'] = 'structure'
        self.reject()


class ProtectedDefinitionEvidence(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.project = pathlib.Path(temp.name) / 'project'
        shutil.copytree(ROOT / 'topology/banach-mazur-baire', self.project,
                        ignore=shutil.ignore_patterns('.lake', '__pycache__'))
        self.file = self.project / 'verification/material-imported-definitions.json'
        self.data = json.loads(self.file.read_text())

    def test_actual_protected_nonempty_definition_passes(self):
        result = check(self.project)
        self.assertIn('Set.Nonempty', result['material_declarations'])

    def test_protected_definition_cannot_be_claimed_as_class(self):
        row = next(d for d in self.data['material_declarations'] if d['name'] == 'Set.Nonempty')
        row['declaration_kind'] = 'class'
        row['bridge_kind'] = 'class-fields'
        self.file.write_text(json.dumps(self.data))
        with self.assertRaises(ValueError):
            check(self.project)

    def test_protected_token_inside_other_text_is_not_a_declaration(self):
        source = next(f for f in self.data['source_files'] if f['path'] == 'Mathlib/Data/Set/Defs.lean')
        excerpt = source['excerpts'][0]
        old = excerpt['text']
        excerpt['text'] = old.replace('protected def Nonempty', 'fake protected def Nonempty')
        excerpt['sha256'] = sha(excerpt['text'].encode())
        doc = self.project / self.data['documentation']
        doc.write_text(doc.read_text().replace(old, excerpt['text']))
        self.file.write_text(json.dumps(self.data))
        with self.assertRaises(ValueError):
            check(self.project)


class NoncomputableDefinitionEvidence(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.project = pathlib.Path(temp.name) / 'project'
        shutil.copytree(ROOT / 'topology/choquet-baire-product', self.project,
                        ignore=shutil.ignore_patterns('.lake', '__pycache__'))
        self.file = self.project / 'verification/material-imported-definitions.json'
        self.data = json.loads(self.file.read_text())

    def test_actual_noncomputable_diameter_passes(self):
        result = check(self.project)
        self.assertIn('Metric.diam', result['material_declarations'])

    def test_noncomputable_definition_cannot_be_claimed_as_class(self):
        row = next(d for d in self.data['material_declarations'] if d['name'] == 'Metric.diam')
        row['declaration_kind'] = 'class'
        row['bridge_kind'] = 'class-fields'
        self.file.write_text(json.dumps(self.data))
        with self.assertRaises(ValueError):
            check(self.project)

    def test_noncomputable_token_inside_other_text_is_rejected(self):
        row = next(d for d in self.data['material_declarations'] if d['name'] == 'Metric.diam')
        excerpt = next(e for f in self.data['source_files'] for e in f['excerpts']
                       if e['name'] == row['definition_excerpt'])
        old = excerpt['text']
        excerpt['text'] = old.replace('noncomputable def diam', 'unsafe noncomputable def diam')
        self.assertNotEqual(old, excerpt['text'])
        excerpt['sha256'] = sha(excerpt['text'].encode())
        doc = self.project / self.data['documentation']
        doc.write_text(doc.read_text().replace(old, excerpt['text']))
        self.file.write_text(json.dumps(self.data))
        with self.assertRaises(ValueError):
            check(self.project)


class StrongChoquetQualifiedEvidence(ImportedDefinitionEvidence):
    PACKAGE = 'topology/strong-choquet-polish'

    def test_root_qualified_class_and_attribute_prefix_pass(self):
        result = check(self.project)
        self.assertIn('SecondCountableTopology', result['material_declarations'])
        self.assertIn('SeparableSpace', result['material_declarations'])

    def test_attribute_token_inside_other_text_rejected(self):
        row = next(d for d in self.data['material_declarations'] if d['name'] == 'SeparableSpace')
        excerpt = next(e for f in self.data['source_files'] for e in f['excerpts']
                       if e['name'] == row['definition_excerpt'])
        old = excerpt['text']
        excerpt['text'] = old.replace('@[mk_iff] class', 'fake @[mk_iff] class')
        self.assertNotEqual(old, excerpt['text'])
        excerpt['sha256'] = sha(excerpt['text'].encode())
        doc = self.project / self.data['documentation']
        doc.write_text(doc.read_text().replace(old, excerpt['text']))
        self.file.write_text(json.dumps(self.data))
        with self.assertRaises(ValueError): check(self.project)


if __name__ == '__main__':
    unittest.main()
