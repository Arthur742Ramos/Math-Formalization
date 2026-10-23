"""Check ordered #print axioms output, including definition/instance reports."""
import re


def check_reports(audit_source, output, permitted):
    expected = re.findall(r'^\s*#print\s+axioms\s+(\S+)\s*$', audit_source, re.M)
    if not expected or len(expected) != len(set(expected)):
        raise ValueError('Audit source must select distinct named declarations')
    pattern = re.compile(
        r"^'(.+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)[ \t]*$",
        re.M,
    )
    reports = []
    for match in pattern.finditer(output):
        body = (match[2] or '').strip()
        axioms = [item.strip() for item in body.split(',')] if body else []
        if any(not item for item in axioms) or len(axioms) != len(set(axioms)):
            raise ValueError('Malformed or duplicate axiom list for '+match[1])
        if not set(axioms) <= set(permitted):
            raise ValueError('Unapproved axioms for '+match[1]+': '+repr(axioms))
        reports.append({'name': match[1], 'axioms': axioms})
    if [row['name'] for row in reports] != expected:
        raise ValueError('Axiom report names/order/count differ from the exact audit source')
    remainder = pattern.sub('', output)
    if remainder.strip():
        raise ValueError('Unexpected output outside ordered axiom reports')
    return {'reports': reports, 'report_count': len(reports),
            'empty_reports': sum(not row['axioms'] for row in reports),
            'permitted_axioms': list(permitted)}
