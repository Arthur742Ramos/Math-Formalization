"""Generate the protected Challenge from the credited, visible proof sources."""
from pathlib import Path
import sys

p = Path(__file__).resolve().parents[1]
header = '''module
public import Mathlib.Topology.MetricSpace.Perfect
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Data.Fintype.Vector
public import Mathlib.Tactic

/- The following Mycielski proof sections are copied from the credited local
   sources. See ATTRIBUTION.md for the original source and authorship. -/
'''
parts = [header]
for name in ('Mycielski/FusionStep.lean', 'Mycielski/Scheme.lean',
             'Mycielski/Independent.lean'):
    source = (p / name).read_text(encoding='utf-8')
    marker = 'public section\n'
    if source.count(marker) != 1:
        raise ValueError(f'Unexpected source structure: {name}')
    parts.append(f'\n/- Source: {name} -/\n' + marker + source.split(marker, 1)[1])
source = (p / 'CantorChaos.lean').read_text(encoding='utf-8')
marker = '@[expose] public section\n'
if source.count(marker) != 1:
    raise ValueError('Unexpected CantorChaos source structure')
parts.append('\n/- Source: CantorChaos.lean; see ATTRIBUTION.md. -/\n' + marker +
             source.split(marker, 1)[1])
output = ''.join(parts)
challenge = p / 'ChaosChallenge.lean'
if sys.argv[1:] == ['--write']:
    challenge.write_text(output, encoding='utf-8', newline='\n')
elif sys.argv[1:] == ['--check']:
    if challenge.read_text(encoding='utf-8') != output:
        raise SystemExit('Challenge differs from credited source sections')
    print('Self-contained Challenge matches credited proof sections.')
else:
    raise SystemExit('Use --write or --check')
