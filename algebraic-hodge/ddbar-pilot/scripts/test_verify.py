"""Regression cases for fail-closed transitive axiom audit parsing."""
import unittest
import tempfile
from pathlib import Path
from unittest.mock import patch
import verify
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


class ReceiptHistory(unittest.TestCase):
    def test_existing_receipt_cannot_be_overwritten(self):
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            receipt = directory / 'local-report.json'
            receipt.write_bytes(b'immutable historical receipt')
            with patch.object(verify, 'OUT', directory):
                with self.assertRaisesRegex(AssertionError, 'Refusing to overwrite'):
                    verify.main()
            self.assertEqual(receipt.read_bytes(), b'immutable historical receipt')


if __name__ == '__main__':
    unittest.main()
