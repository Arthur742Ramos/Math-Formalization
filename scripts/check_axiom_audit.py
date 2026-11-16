"""Check a fresh transitive axiom log for the entire selected surface.

This checks log contents; the caller must bind a successful Lean command and
its exact source/toolchain to the log. Historical logs do not certify new code.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
PHYSICAL = ['ErdosOverlap.Certificate.FrontierCover.denominator_bound',
            'ErdosOverlap.Certificate.FrontierCover.nativeRows_physical']


def check(package, log):
    config = json.loads((package/'comparator.json').read_text())
    if set(config['permitted_axioms']) != STANDARD:
        raise ValueError('The selected axiom allowlist differs from the standard three')
    if config['definition_names']:
        raise ValueError('The fixed model definitions must not be declared as definition holes')
    fixed = json.loads((package/'verification/fixed-definitions.json').read_text())
    if fixed['schema_version'] != 1:
        raise ValueError('Unsupported fixed-definition inventory')
    expected = config['theorem_names'] + fixed['fixed_definition_names'] + PHYSICAL
    if len(expected) != len(set(expected)):
        raise ValueError('Duplicate selected axiom target')
    pattern = re.compile(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)")
    reports = {}
    for match in pattern.finditer(log):
        name = match[1]
        if name in reports:
            raise ValueError('Duplicate axiom report: '+name)
        axioms = [s.strip() for s in (match[2] or '').split(',') if s.strip()]
        if set(axioms) - STANDARD:
            raise ValueError('Unapproved transitive axiom: '+name)
        reports[name] = axioms
    if pattern.sub('', log).strip():
        raise ValueError('Unrecognized output in axiom log')
    if set(reports) != set(expected):
        raise ValueError('Missing or unexpected axiom reports: '+str(set(reports)^set(expected)))
    return {'status': 'pass', 'scope': 'Axiom-log consistency; run/source provenance is external',
            'selected_theorems': len(config['theorem_names']),
            'fixed_definitions': len(fixed['fixed_definition_names']),
            'physical_certificate_targets': len(PHYSICAL), 'axioms': reports,
            'log_sha256': hashlib.sha256(log.encode()).hexdigest()}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--package', type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument('--axiom-log', type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(check(args.package, args.axiom_log.read_text()), indent=2))
