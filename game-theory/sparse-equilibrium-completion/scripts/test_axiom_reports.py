"""Negative controls for exact ordered axiom-report validation."""
import json
import sys
from check_axiom_reports import check_reports

if not __debug__ or sys.flags.optimize:
    raise SystemExit('Axiom report controls require assertions')

fixtures = [
    ('apostrophe-and-multiline', "#print axioms X.a'\n#print axioms X.b\n",
     "'X.a\'' depends on axioms: [propext,\n Classical.choice]\n'X.b' does not depend on any axioms\n", True),
    ('unapproved', '#print axioms X.a\n', "'X.a' depends on axioms: [Bad]\n", False),
    ('extra', '#print axioms X.a\n',
     "'X.a' depends on axioms: [propext]\n'X.b' does not depend on any axioms\n", False),
    ('missing', '#print axioms X.a\n', '', False),
    ('unexpected-output', '#print axioms X.a\n',
     "warning: stale\n'X.a' does not depend on any axioms\n", False),
    ('reordered', '#print axioms X.a\n#print axioms X.b\n',
     "'X.b' does not depend on any axioms\n'X.a' does not depend on any axioms\n", False),
    ('duplicate-source', '#print axioms X.a\n#print axioms X.a\n',
     "'X.a' does not depend on any axioms\n'X.a' does not depend on any axioms\n", False),
    ('malformed-trailing-comma', '#print axioms X.a\n',
     "'X.a' depends on axioms: [propext,,]\n", False),
    ('comma-only-list', '#print axioms X.a\n', "'X.a' depends on axioms: [,,,]\n", False),
    ('duplicate-axiom', '#print axioms X.a\n',
     "'X.a' depends on axioms: [propext, propext]\n", False),
    ('duplicate-output', '#print axioms X.a\n',
     "'X.a' does not depend on any axioms\n'X.a' does not depend on any axioms\n", False),
]
for name, source, output, expected in fixtures:
    try:
        check_reports(source, output, ['propext', 'Quot.sound', 'Classical.choice'])
        actual = True
    except ValueError:
        actual = False
    assert actual == expected, name
print(json.dumps({'result': 'pass', 'controls': [fixture[0] for fixture in fixtures]}))
