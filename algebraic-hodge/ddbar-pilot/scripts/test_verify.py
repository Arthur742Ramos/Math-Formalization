"""Regression cases for fail-closed transitive axiom audit parsing."""
import unittest
from verify import parse_audit


class AuditParsing(unittest.TestCase):
    def test_wrapped_axioms_and_axiom_free(self):
        output = "'A' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'B' does not depend on any axioms"
        self.assertEqual(parse_audit(output, ['A', 'B']),
                         {'A': ['Classical.choice', 'Quot.sound', 'propext'], 'B': []})

    def test_custom_axiom_rejected(self):
        with self.assertRaises(AssertionError):
            parse_audit("'A' depends on axioms: [propext, invented_result]", ['A'])

    def test_missing_declaration_rejected(self):
        with self.assertRaises(AssertionError):
            parse_audit("'A' does not depend on any axioms", ['A', 'B'])

    def test_extra_or_duplicate_declaration_rejected(self):
        with self.assertRaises(AssertionError):
            parse_audit("'A' does not depend on any axioms\n'B' does not depend on any axioms", ['A'])
        with self.assertRaises(AssertionError):
            parse_audit("'A' does not depend on any axioms\n'A' does not depend on any axioms", ['A'])


if __name__ == '__main__':
    unittest.main()
