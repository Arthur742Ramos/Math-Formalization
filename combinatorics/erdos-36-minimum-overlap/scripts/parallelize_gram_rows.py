"""Remove scheduling-only predecessor imports from selected Gram checks.

Individual generated row modules cease to re-export predecessor rows; the
family aggregator continues to export every original theorem. Proof bodies,
types, data, options and the ordinary-kernel decisions are unchanged.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re


def digest(data):
    return hashlib.sha256(data.encode()).hexdigest()


def transform(package, families):
    gram = package/'ErdosOverlap/Gram'
    changed = []
    for family in families:
        assert re.fullmatch(r'Native6(?:Raw|PSD)\d\d', family)
        paths = sorted(gram.glob(f'{family}Rows[0-9][0-9].lean'))
        assert paths
        for index, path in enumerate(paths):
            original = path.read_text()
            imports = re.findall(r'^public import (\S+)', original, re.M)
            assert imports == [f'ErdosOverlap.Gram.{family}Data'] or imports == [f'ErdosOverlap.Gram.{family}Rows{index-1:02d}']
            rewritten = re.sub(r'^public import \S+', f'public import ErdosOverlap.Gram.{family}Data', original, count=1, flags=re.M)
            rewritten = rewritten.replace('small, sequentially imported modules bounds the kernel\'s temporary memory.',
                'small independent modules allows bounded parallel scheduling.')
            if original != rewritten:
                path.write_text(rewritten)
                changed.append({'path': str(path.relative_to(package)), 'before_sha256': digest(original),
                                'after_sha256': digest(rewritten)})
        aggregate = gram/f'{family}.lean'
        original = aggregate.read_text()
        pattern = rf'^public import ErdosOverlap\.Gram\.{family}Rows\d\d$'
        existing = re.findall(pattern, original, re.M)
        expected = [f'public import ErdosOverlap.Gram.{p.stem}' for p in paths]
        if existing == expected:
            continue
        assert existing == expected[-1:]
        rewritten = re.sub(pattern, '\n'.join(expected), original, count=1, flags=re.M)
        aggregate.write_text(rewritten)
        changed.append({'path': str(aggregate.relative_to(package)), 'before_sha256': digest(original),
                        'after_sha256': digest(rewritten)})
    return changed


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--package', type=Path, default=Path(__file__).resolve().parent.parent)
    p.add_argument('--families', nargs='+', default=['Native6Raw14'])
    p.add_argument('--receipt', type=Path)
    a = p.parse_args()
    changed = transform(a.package, a.families)
    report = {'families': a.families, 'scope': 'Imports and scheduling comments only; all declaration bodies unchanged.', 'files': changed}
    if a.receipt:
        a.receipt.write_text(json.dumps(report, indent=2)+'\n')
    print(f'Updated {len(changed)} files in {len(a.families)} families.')
