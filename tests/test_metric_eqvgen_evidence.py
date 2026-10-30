"""Focused controls for the pinned equivalence-closure evidence exception."""
import copy
import json
import pathlib
import sys
import unittest
from unittest.mock import patch

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from check_imported_definitions import check_eqvgen_kind, check_pinned_eqvgen, declaration_header_matches
import check_imported_definitions as checker


class EqvGenEvidence(unittest.TestCase):
    def setUp(self):
        self.decl = {'name': 'Relation.EqvGen', 'bridge_kind': 'inductive-constructors',
                     'constructors': ['rel', 'refl', 'symm', 'trans']}
        self.dep = {'name': 'mathlib', 'repository': 'https://github.com/leanprover-community/mathlib4',
                    'commit': '065356127b1dc0016f66b7283ce0ce2c4055aa55'}
        self.source = {'path': 'Mathlib/Logic/Relation.lean',
                       'sha256': '2b678f33904c7e073de526d9d3243909e5d7d72bc0eed7f4cf9e65f443b72547',
                       'git_blob_sha1': '173394c4bb2a511bb02a538e31a015e9393eb7b5'}
        self.excerpt = {'first_line': 408, 'last_line': 417,
                        'sha256': 'c22edd47d0fe6052783b4dc8ed85c4f7a58a9bb3e0fa5989d14990181b4da46a',
                        'text': 'variable (r) in\n/-- `EqvGen r`: equivalence closure of `r`. -/\n'
                        '@[mk_iff]\ninductive EqvGen : α → α → Prop\n'
                        '  | rel x y : r x y → EqvGen x y\n'
                        '  | refl x : EqvGen x x\n'
                        '  | symm x y : EqvGen x y → EqvGen y x\n'
                        '  | trans x y z : EqvGen x y → EqvGen y z → EqvGen x z\n\n'
                        'attribute [mk_iff] TransGen\n'}

    def test_pinned_inductive_and_legacy_unrelated_names(self):
        check_eqvgen_kind('Relation.EqvGen', 'inductive', 2)
        check_eqvgen_kind('Other.Name', 'def', 1)
        check_eqvgen_kind('Other.Name', 'def', 2)
        check_pinned_eqvgen(self.decl, self.dep, self.source, self.excerpt)
        self.assertTrue(declaration_header_matches(self.excerpt['text'], 'inductive', 'Relation.EqvGen'))

    def test_wrong_name_kind_and_schema_fail(self):
        for args in [('Relation.EqvGen', 'def', 1), ('Relation.EqvGen', 'def', 2),
                     ('Other.EqvGen', 'inductive', 2)]:
            with self.subTest(args=args), self.assertRaises(ValueError):
                check_eqvgen_kind(*args)

    def test_constructor_and_source_mutations_fail(self):
        mutations = [(0, 'name', 'Other.EqvGen'), (0, 'bridge_kind', 'literal-unfolding'),
                     (0, 'constructors', ['rel', 'refl', 'trans']),
                     (0, 'constructors', ['refl', 'rel', 'symm', 'trans']),
                     (0, 'constructors', ['rel', 'refl', 'symm', 'trans', 'extra']),
                     (1, 'commit', '0' * 40), (2, 'path', 'Mathlib/Logic/Other.lean'),
                     (2, 'sha256', '0' * 64), (2, 'git_blob_sha1', '0' * 40),
                     (3, 'first_line', 409), (3, 'last_line', 416),
                     (3, 'text', self.excerpt['text'].replace('| refl', '| altered'))]
        for index, key, value in mutations:
            args = copy.deepcopy([self.decl, self.dep, self.source, self.excerpt])
            args[index][key] = value
            with self.subTest(index=index, key=key), self.assertRaises(ValueError):
                check_pinned_eqvgen(*args)


class EqvGenFullCheck(EqvGenEvidence):
    """Exercise check() in memory; filesystem safety and origin are separate."""

    def fixture(self, version=2, name='Relation.EqvGen', kind='inductive', text=None):
        if text is None:
            text = self.excerpt['text']
        first, last = 408, 407 + len(text.splitlines())
        source_url = self.dep['repository'] + '/blob/' + self.dep['commit'] + '/' + self.source['path']
        excerpt_url = source_url + f'#L{first}-L{last}'
        excerpt = {'name': 'selected', 'first_line': first, 'last_line': last, 'text': text,
                   'sha256': checker.sha(text.encode()), 'url': excerpt_url}
        header = '/-\nCopyright synthetic fixture\nApache 2.0\n-/\n'
        source = {**self.source, 'url': source_url, 'license': 'Apache-2.0',
                  'upstream_header': header, 'excerpts': [excerpt]}
        decl = {'name': name, 'role': 'hypothesis', 'meaning': 'Synthetic fixture only',
                'used_by': ['Selected.result'], 'definition_excerpt': 'selected',
                'declaration_kind': kind,
                'bridge_kind': 'inductive-constructors' if kind == 'inductive' else 'literal-unfolding',
                'constructors': ['rel', 'refl', 'symm', 'trans'], 'bridge_excerpts': ['selected'],
                'dependency_expansion': 'Synthetic fixture', 'proof_status': 'Not compiled'}
        if version == 1:
            decl.update(bridge_kind='proved-equivalence', semantic_bridge_excerpt='selected',
                        complement_excerpt='selected')
        modules = {'ChallengeMaterial.lean': 'public import Challenge\n-- BEGIN material-imported-definition audit\n-- END material-imported-definition audit\n',
                   'SolutionMaterial.lean': 'public import Solution\n-- BEGIN material-imported-definition audit\n-- END material-imported-definition audit\n'}
        dep = {**self.dep, 'lean_toolchain': 'test-toolchain'}
        manifest = {'schema_version': version, 'dependency': dep, 'documentation': 'MATERIAL.md',
                    'required_declarations': [name], 'material_declarations': [decl],
                    'source_files': [source],
                    'checked_bridge_modules': [{'path': p, 'module': p[:-5],
                                                'sha256': checker.sha(body.encode())}
                                               for p, body in modules.items()]}
        doc = '\n'.join([source_url, source['sha256'], header, excerpt_url, text, name, 'Selected.result'])
        return {'verification/material-imported-definitions.json': json.dumps(manifest),
                'lake-manifest.json': json.dumps({'packages': [{'name': 'mathlib', 'rev': self.dep['commit'],
                                                               'url': self.dep['repository']}]}),
                'lean-toolchain': 'test-toolchain',
                'comparator.json': json.dumps({'challenge_module': 'Challenge', 'solution_module': 'Solution',
                                               'theorem_names': ['Selected.result'], 'definition_names': []}),
                'MATERIAL.md': doc, 'lakefile.toml': 'defaultTargets = ["ChallengeMaterial", "SolutionMaterial"]\n',
                **modules}

    def checked(self, files):
        class MemoryFile:
            def __init__(self, value): self.value = value
            def read_text(self): return self.value
            def read_bytes(self): return self.value.encode()
        def lookup(_root, name):
            if name not in files:
                raise ValueError('missing synthetic file')
            return MemoryFile(files[name])
        with patch.object(checker, 'local_file', side_effect=lookup):
            return checker.check('synthetic-project')

    def test_pinned_fixture_and_unrelated_legacy_examples(self):
        self.assertEqual(self.checked(self.fixture())['upstream_origin'], 'not-checked')
        for version in (1, 2):
            with self.subTest(version=version):
                self.assertEqual(self.checked(self.fixture(version, 'Other.Example', 'def',
                                                           'def Example : Prop := True\n'))['status'], 'pass')

    def test_wrong_kind_and_v1_downgrade_rejected(self):
        forged = 'def EqvGen : Prop := True\n'
        fixtures = [(self.fixture(2, 'Relation.EqvGen', 'def', forged), 'Unsupported inductive name'),
                    (self.fixture(1, 'Relation.EqvGen', 'def', forged), 'requires the pinned inductive schema'),
                    (self.fixture(2, 'Other.EqvGen', 'inductive'), 'Unsupported inductive name')]
        for files, expected in fixtures:
            with self.subTest(expected=expected), self.assertRaisesRegex(ValueError, expected):
                self.checked(files)

    def test_missing_and_unbuilt_bridges_rejected(self):
        files = self.fixture()
        del files['SolutionMaterial.lean']
        with self.assertRaisesRegex(ValueError, 'missing synthetic file'):
            self.checked(files)
        files = self.fixture()
        files['lakefile.toml'] = 'defaultTargets = ["ChallengeMaterial"]\n'
        with self.assertRaisesRegex(ValueError, 'Bridge module not built by default'):
            self.checked(files)

    def test_constructor_and_bridge_contract_rejected_by_full_check(self):
        for key, value, expected in [
            ('constructors', ['refl', 'rel', 'symm', 'trans'], 'Unsupported inductive contract'),
            ('bridge_kind', 'literal-unfolding', 'Unsupported inductive contract'),
            ('bridge_excerpts', ['missing'], 'Missing or invalid semantic bridge evidence'),
        ]:
            files = self.fixture()
            manifest = json.loads(files['verification/material-imported-definitions.json'])
            manifest['material_declarations'][0][key] = value
            files['verification/material-imported-definitions.json'] = json.dumps(manifest)
            with self.subTest(key=key), self.assertRaisesRegex(ValueError, expected):
                self.checked(files)

    def test_forged_inductive_body_rejected_after_internal_hash_update(self):
        altered = self.excerpt['text'].replace('r x y → EqvGen x y', 'r y x → EqvGen x y')
        with self.assertRaisesRegex(ValueError, 'Pinned inductive source/constructor excerpt mismatch'):
            self.checked(self.fixture(text=altered))

    def test_mixed_entrypoint_rejected_even_with_updated_bridge_hash(self):
        files = self.fixture()
        files['ChallengeMaterial.lean'] += 'public import Solution\n'
        manifest = json.loads(files['verification/material-imported-definitions.json'])
        manifest['checked_bridge_modules'][0]['sha256'] = checker.sha(files['ChallengeMaterial.lean'].encode())
        files['verification/material-imported-definitions.json'] = json.dumps(manifest)
        with self.assertRaisesRegex(ValueError, 'Mixed duplicate entrypoints'):
            self.checked(files)


if __name__ == '__main__':
    unittest.main()
