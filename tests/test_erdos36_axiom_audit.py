"""Negative controls for the complete selected-surface axiom-log gate."""
import importlib.util
import json
from pathlib import Path
import unittest

PACKAGE = Path(__file__).resolve().parents[1]/'combinatorics/erdos-36-minimum-overlap'
spec = importlib.util.spec_from_file_location('erdos_audit', PACKAGE/'scripts/check_axiom_audit.py')
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)


class CompleteAxiomLog(unittest.TestCase):
    def fixture(self):
        config = json.loads((PACKAGE/'comparator.json').read_text())
        fixed = json.loads((PACKAGE/'verification/fixed-definitions.json').read_text())
        names = config['theorem_names']+fixed['fixed_definition_names']+audit.PHYSICAL
        return '\n'.join("'"+name+"' depends on axioms: [propext,\n Classical.choice, Quot.sound]"
                         for name in names)+'\n'

    def test_synthetic_complete_multiline_and_axiom_free_reports(self):
        log = self.fixture().replace('depends on axioms: [propext,\n Classical.choice, Quot.sound]',
                                     'does not depend on any axioms', 1)
        result = audit.check(PACKAGE, log)
        self.assertEqual((result['selected_theorems'], result['fixed_definitions']), (11, 15))

    def test_missing_selected_definition_is_rejected(self):
        log = self.fixture()
        start = log.index("'ErdosOverlap.Discrete.minimumOverlapQuotient'")
        end = log.index(']', start)+1
        with self.assertRaisesRegex(ValueError, 'Missing or unexpected'):
            audit.check(PACKAGE, log[:start]+log[end:])

    def test_sorry_ax_duplicate_and_hidden_error_are_rejected(self):
        good = self.fixture()
        for log in [good.replace('Quot.sound', 'sorryAx', 1),
                    good+good[:good.index(']')+1], good+'error: failed proof\n']:
            with self.subTest(log=log[-80:]), self.assertRaises(ValueError):
                audit.check(PACKAGE, log)


if __name__ == '__main__':
    unittest.main()
