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


if __name__ == '__main__':
    unittest.main()
