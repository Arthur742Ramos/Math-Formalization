"""Assess proposed integral totals by exact endpoint arithmetic, before Lean replay."""
import argparse
from fractions import Fraction as F
import gzip
import hashlib
import json
from pathlib import Path
import re


def assess(package, packet_path, compact_path, output):
    with gzip.open(packet_path, 'rt') as stream:
        packet = json.load(stream)
    totals = {k: F(v) for k, v in packet['totals'].items()}
    compact = json.loads(compact_path.read_text())
    data = (package/'ErdosOverlap/Certificate/FrontierKernelData.lean').read_text()
    c = F(re.search(r'def meanCoefficientExact : ℚ := \(([^:]+) : ℚ\)', data)[1].replace(' ', ''))
    normalization = package/'ErdosOverlap/FrontierNormalization.lean'
    L = F(re.search(r'def lowerAtZeroBound : ℚ := \(([^:]+) : ℚ\)', normalization.read_text())[1].replace(' ', ''))
    target, height = F(3806279907, 10**10), F(380627990701, 10**12)
    rows = []
    for row in compact['rows']:
        name = row['name']
        if name.startswith('outer'):
            a, b, rc, d = (F(row[k]) for k in ['a', 'b', 'c', 'd'])
        else:
            mode = None if name == 'central' else int(name[7:])
            kind = 'Central' if mode is None else f'Profile{mode:02d}'
            a = L+totals[kind]-(F(packet['iv'][mode]) if mode is not None else 0)
            b = F(packet['tau'][mode]) if mode is not None else F(0)
            rc, d = c, totals['Denominator']
        lo, hi = F(row['lo']), F(row['hi'])
        assert d > 0 and rc <= 0 and lo <= hi
        floor = min((a+b*x+rc*x*x)/d for x in [lo, hi])
        rows.append(dict(name=name, lo=lo, hi=hi, a=a, b=b, c=rc, d=d,
                         floor=floor, height_margin=floor-height))
    assert rows[0]['lo'] == 0 and rows[-1]['hi'] == F(9, 2560)
    assert all(a['hi'] == b['lo'] for a, b in zip(rows, rows[1:]))
    floor = min(r['floor'] for r in rows)
    report = dict(scope='Exact native-row proposal assessment; outer rows separate; no Lean verification claimed',
                  target=target, height=height, floor=floor, margin=floor-height,
                  pass_proposal=floor>height, rows=rows,
                  geometries=len(packet['geometries']), patches=len(packet['patches']),
                  leaves={k:len(v) for k,v in packet['leaves'].items()},
                  totals=totals, input_sha256={str(p):hashlib.sha256(p.read_bytes()).hexdigest()
                    for p in [packet_path, compact_path, normalization,
                              package/'ErdosOverlap/Certificate/FrontierKernelData.lean', Path(__file__)]})
    output.write_text(json.dumps(report, default=str, indent=2)+'\n')
    print(json.dumps({k:(float(v) if isinstance(v, F) else v) for k,v in report.items()
                      if k not in ['rows', 'totals', 'leaves']}, indent=2))
    if floor <= height:
        raise SystemExit('Proposed bounds do not prove the target.')


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--package', type=Path, default=Path(__file__).resolve().parent.parent)
    p.add_argument('--packet', type=Path, required=True)
    p.add_argument('--compact', type=Path,
                   help='Interval/mode proposal (default: retained certificates/frontier/cover-proposal.json)')
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    assess(a.package, a.packet, a.compact or a.package/'certificates/frontier/cover-proposal.json', a.output)
