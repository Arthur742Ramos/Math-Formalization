"""Regression controls for complete Lean declaration identifiers."""
import unittest
from check_imported_definitions import declaration_head_matches


class DeclarationIdentifierTests(unittest.TestCase):
    def test_exact_primed_names(self):
        for legacy in (False, True):
            for name in ("max'", "sup'"):
                with self.subTest(legacy=legacy, name=name):
                    self.assertTrue(declaration_head_matches('Finset.'+name, 'def',
                        'def '+name+' (s : Finset α) : α := value\n', legacy=legacy))

    def test_namespace_and_modifiers(self):
        self.assertTrue(declaration_head_matches("Finset.max'", 'def',
            "@[expose] protected noncomputable def Finset.max' (s : Finset α) := value\n"))

    def test_rejects_identifier_continuations(self):
        for legacy in (False, True):
            for suffix in ("'", '!', '?', '.helper', '_other', 'other', '₀'):
                with self.subTest(legacy=legacy, suffix=suffix):
                    self.assertFalse(declaration_head_matches("Finset.max'", 'def',
                        "def max'"+suffix+' (s : Finset α) := value\n', legacy=legacy))

    def test_ordinary_name_cannot_match_primed_name(self):
        for legacy in (False, True):
            self.assertFalse(declaration_head_matches('Finset.max', 'def',
                "def max' (s : Finset α) := value\n", legacy=legacy))

    def test_exact_inductive_and_wrong_kind(self):
        body = ('inductive ReflTransGen (r : α → α → Prop) (a : α) : α → Prop\n'
                '  | refl : ReflTransGen r a a\n')
        self.assertTrue(declaration_head_matches('Relation.ReflTransGen', 'inductive', body))
        self.assertFalse(declaration_head_matches('Relation.ReflTransGen', 'def', body))
        self.assertFalse(declaration_head_matches('Relation.ReflTransGen', 'inductive',
            body.replace('inductive ReflTransGen ', 'inductive ReflTransGen_other ')))
        self.assertFalse(declaration_head_matches('Relation.ReflTransGen', 'inductive',
            body.replace('inductive ReflTransGen ', '-- inductive ReflTransGen ')))

    def test_wrong_kind_or_commented_declaration(self):
        self.assertFalse(declaration_head_matches("Finset.max'", 'def',
            "theorem max' : True := trivial\n"))
        self.assertFalse(declaration_head_matches("Finset.max'", 'def',
            "-- def max' (s : Finset α) := value\n"))


from copy import deepcopy
from check_imported_definitions import generated_definition_bridge

# Synthetic export-record fixtures test schema rejection only; actual provenance
# is authenticated separately against retained exports and exact pinned sources.
PIN = '065356127b1dc0016f66b7283ce0ce2c4055aa55'
COMPILER = '11acb17ec6b07a8f9e9173e6845197929540936b'
PROPOSAL = {'new_material_records': [{'name': 'abs', 'declaration_kind': 'def', 'definition_excerpt': 'mabs additive absolute-value generator', 'generated_from': {'producer_attribute': 'to_additive', 'generator_name': 'mabs', 'generator_declaration_kind': 'def', 'generator_excerpt': 'mabs additive absolute-value generator', 'expected_target_name': 'abs', 'generated_declaration_evidence': {'path': 'follow-on/generated-abs-single-existing-export-attestation-v1.json', 'sha256': '174b84d6bf356b7a92cd5102a0d30391f7eff4ba93cf26505dce92d70c754641', 'exact_exported_name': 'abs', 'declaration_kind': 'def'}, 'checked_semantic_bridge': 'generated_abs_rational_semantics'}, 'bridge_kind': 'proved-equivalence'}, {'name': 'Pi.single', 'declaration_kind': 'def', 'definition_excerpt': 'Pi.mulSingle additive single-coordinate generator', 'generated_from': {'producer_attribute': 'to_additive', 'generator_name': 'Pi.mulSingle', 'generator_declaration_kind': 'def', 'generator_excerpt': 'Pi.mulSingle additive single-coordinate generator', 'expected_target_name': 'Pi.single', 'generated_declaration_evidence': {'path': 'follow-on/generated-abs-single-existing-export-attestation-v1.json', 'sha256': '174b84d6bf356b7a92cd5102a0d30391f7eff4ba93cf26505dce92d70c754641', 'exact_exported_name': 'Pi.single', 'declaration_kind': 'def'}, 'checked_semantic_bridge': 'generated_single_real_semantics'}, 'bridge_kind': 'proved-equivalence'}]}
EVIDENCE = {'schema_version': 1, 'compiler_commit': '11acb17ec6b07a8f9e9173e6845197929540936b', 'mathlib_commit': '065356127b1dc0016f66b7283ce0ce2c4055aa55', 'exports': {'solution.ndjson': {'sha256': '1111111111111111111111111111111111111111111111111111111111111111', 'bytes': 1, 'declarations': {'abs': {'kind': 'def', 'resolved_name': 'abs', 'name_id': 1, 'type_expression_root': 0, 'value_expression_root': 1, 'raw_record_sha256': '0000000000000000000000000000000000000000000000000000000000000000'}, 'Pi.single': {'kind': 'def', 'resolved_name': 'Pi.single', 'name_id': 1, 'type_expression_root': 0, 'value_expression_root': 1, 'raw_record_sha256': '0000000000000000000000000000000000000000000000000000000000000000'}}}, 'challenge.ndjson': {'sha256': '1111111111111111111111111111111111111111111111111111111111111111', 'bytes': 1, 'declarations': {'abs': {'kind': 'def', 'resolved_name': 'abs', 'name_id': 1, 'type_expression_root': 0, 'value_expression_root': 1, 'raw_record_sha256': '0000000000000000000000000000000000000000000000000000000000000000'}, 'Pi.single': {'kind': 'def', 'resolved_name': 'Pi.single', 'name_id': 1, 'type_expression_root': 0, 'value_expression_root': 1, 'raw_record_sha256': '0000000000000000000000000000000000000000000000000000000000000000'}}}}}
SOURCES = {'mabs additive absolute-value generator': ('Mathlib/Algebra/Order/Group/Unbundled/Abs.lean', 'variable {α : Type*}\n\nsection Lattice\nvariable [Lattice α]\n\nsection Group\nvariable [Group α] {a b : α}\n\n/-- `mabs a`, denoted `|a|ₘ`, is the absolute value of `a`. -/\n@[to_additive (attr := grind) /-- `abs a`, denoted `|a|`, is the absolute value of `a` -/]\ndef mabs (a : α) : α := a ⊔ a⁻¹\n'), 'Pi.mulSingle additive single-coordinate generator': ('Mathlib/Algebra/Notation/Pi/Basic.lean', "variable {ι ι' α : Type*} {M N O : ι → Type*}\n\nnamespace Pi\nvariable [∀ i, One (M i)] [∀ i, One (N i)] [∀ i, One (O i)] [DecidableEq ι] {i : ι} {x : M i}\n\n/-- The function supported at `i`, with value `x` there, and `1` elsewhere. -/\n@[to_additive /-- The function supported at `i`, with value `x` there, and `0` elsewhere. -/]\ndef mulSingle (i : ι) (x : M i) : ∀ j, M j := Function.update 1 i x\n\n@[to_additive (attr := simp)]\nlemma mulSingle_eq_same (i : ι) (x : M i) : mulSingle i x i = x := Function.update_self i x _\n")}

class GeneratedDefinitionTests(unittest.TestCase):
    def check(self, row=None, body=None, path=None, evidence=None):
        row = deepcopy(row if row is not None else PROPOSAL['new_material_records'][0])
        source, text = SOURCES[row['definition_excerpt']]
        return generated_definition_bridge(row, text if body is None else body,
            source if path is None else path, EVIDENCE if evidence is None else evidence, COMPILER, PIN)

    def test_actual_two_generators(self):
        for row in PROPOSAL['new_material_records']:
            self.assertEqual(self.check(row), row['generated_from']['checked_semantic_bridge'])

    def test_wrong_metadata(self):
        for key, value in [('generator_name', 'other'), ('producer_attribute', 'other'),
                           ('generator_declaration_kind', 'theorem'), ('expected_target_name', 'other'),
                           ('generator_excerpt', 'other'), ('checked_semantic_bridge', 'bad.name'),
                           ('checked_semantic_bridge','unrelated_true_theorem')]:
            row = deepcopy(PROPOSAL['new_material_records'][0]); row['generated_from'][key] = value
            with self.subTest(key=key), self.assertRaises(ValueError): self.check(row)
        for key, value in [('declaration_kind', 'theorem'), ('bridge_kind', 'literal-unfolding'), ('name','Pi.single')]:
            row = deepcopy(PROPOSAL['new_material_records'][0]); row[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError): self.check(row)

    def test_missing_expected_target(self):
        row = deepcopy(PROPOSAL['new_material_records'][0]); del row['generated_from']['expected_target_name']
        with self.assertRaises(KeyError): self.check(row)

    def test_attached_attribute_only(self):
        accepted = '@[to_additive /-- documentation -/]\ndef mabs (a : A) := a\n'
        self.check(body=accepted)
        for body in ['-- @[to_additive]\ndef mabs (a : A) := a\n',
                     '/- outer /- @[to_additive] -/ comment -/\ndef mabs (a : A) := a\n',
                     'def text := "@[to_additive] def mabs"\ndef mabs (a : A) := a\n',
                     '@[to_additive]\ndef other := 0\ndef mabs (a : A) := a\n',
                     '@[to_additive]\ntheorem mabs : True := trivial\n',
                     '@[not_to_additive]\ndef mabs (a : A) := a\n',
                     '@[to_additive.fake]\ndef mabs (a : A) := a\n',
                     '@[to_additive unexpectedTarget]\ndef mabs (a : A) := a\n',
                     'def text := r#"text \"\n@[to_additive]\ndef mabs (a : A) := a\n\" trailing "#\n',
                     '@[to_additive]\n-- def mabs (a : A) := a\n',
                     '@[to_additive]\ndef Other.mabs (a : A) := a\n']:
            with self.subTest(body=body), self.assertRaises(ValueError): self.check(body=body)

    def test_generator_identifier_continuations(self):
        for suffix in ["'", '!', '?', '_other', '.helper', 'other', '₀']:
            with self.subTest(suffix=suffix), self.assertRaises(ValueError):
                self.check(body='@[to_additive]\ndef mabs'+suffix+' (a : A) := a\n')

    def test_source_path(self):
        with self.assertRaises(ValueError): self.check(path='Mathlib/Other.lean')

    def test_target_evidence_fields(self):
        for key,value in [('exact_exported_name','other'),('declaration_kind','theorem')]:
            row=deepcopy(PROPOSAL['new_material_records'][0]);row['generated_from']['generated_declaration_evidence'][key]=value
            with self.subTest(key=key), self.assertRaises(ValueError): self.check(row)
        for export in ['solution.ndjson','challenge.ndjson']:
            for key,value in [('kind','theorem'),('resolved_name','other'),('raw_record_sha256','bad'),('name_id',False)]:
                e=deepcopy(EVIDENCE); e['exports'][export]['declarations']['abs'][key]=value
                with self.subTest(export=export,key=key), self.assertRaises(ValueError): self.check(evidence=e)
            e=deepcopy(EVIDENCE);del e['exports'][export]['declarations']['abs']
            with self.assertRaises(KeyError): self.check(evidence=e)

    def test_pins_and_export_digest(self):
        for key in ['schema_version','compiler_commit','mathlib_commit']:
            e=deepcopy(EVIDENCE);e[key]='wrong'
            with self.subTest(key=key), self.assertRaises(ValueError): self.check(evidence=e)
        e=deepcopy(EVIDENCE);e['schema_version']=True
        with self.assertRaises(ValueError):self.check(evidence=e)
        e=deepcopy(EVIDENCE);e['exports']['solution.ndjson']['sha256']='bad'
        with self.assertRaises(ValueError):self.check(evidence=e)


if __name__ == '__main__':
    unittest.main()
