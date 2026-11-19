"""Generate exact physical-kernel data for the frozen fully_joint32 candidate.

The generated data include explicit kernel-checked sign and normalization tests.
This generator is not a proof oracle, and does not claim integral bounds.
"""
import argparse
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import re


def rat(value):
    value = F(value)
    return f'({value.numerator} / {value.denominator} : ℚ)'


def header(imports, namespace, source_hash):
    return '''/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

''' + ''.join(f'public import {name}\n' for name in imports) + f'''
/-! Exact data for the fully_joint32 kernel.
Frozen rational input SHA-256: `{source_hash}`.
Generation is not verification; the finite checks below must compile. -/

namespace {namespace}
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

'''


def generate(package):
    cert = package / 'ErdosOverlap/Certificate'
    source = package / 'certificates/frontier/kernel.json'
    data = json.loads(source.read_text())
    assert data['candidate'] == 'fully_joint32'
    source_hash = hashlib.sha256(source.read_bytes()).hexdigest()
    delta = {key: F(value) for key, value in data['delta'].items()}
    rows = []
    for path in sorted(cert.glob('Native6Periodic[0-9][0-9].lean')):
        rows.extend((int(r), int(k), int(i), per == 'true', F(w))
                    for r, k, i, per, w in re.findall(
                        r'⟨(\d+), (\d+), (\d+), (true|false), \((-?\d+/\d+)\)⟩', path.read_text()))
    assert len(rows) == 10087
    net_rows = []
    for index, (r, k, cell, perimeter, old) in enumerate(rows):
        weight = old * (1 + delta.get(f'periodic:{index}', F(0)))
        assert weight <= 0
        if weight:
            net_rows.append((r, k, cell, perimeter, weight))
    for index, descriptor in enumerate(data['new_rows']):
        coefficient = delta.get(f'new_triangle:{index}', F(0))
        assert coefficient >= 0
        if not coefficient:
            continue
        assert descriptor['kind'] == 'triangle' and descriptor['perimeter'] is False
        net_rows.append((descriptor['r'], descriptor['k'], descriptor['cell'], False, -coefficient / 131072))
    assert all(0 < r < k and 0 <= cell < 131072 and weight <= 0
               for r, k, cell, perimeter, weight in net_rows)
    periodic_names = []
    for old in cert.glob('FrontierPeriodic[0-9]*.lean'):
        old.unlink()
    for chunk, start in enumerate(range(0, len(net_rows), 64)):
        name = f'periodic{chunk:03d}'
        periodic_names.append(name)
        block = net_rows[start:start+64]
        text = header(['ErdosOverlap.KernelAssembly'], 'ErdosOverlap.FrontierData', source_hash)
        text += f'def {name} : List PeriodicCellRow := [\n'
        text += ',\n'.join(f'  ⟨{r}, {k}, {cell}, {str(perimeter).lower()}, {rat(weight)}⟩'
                           for r, k, cell, perimeter, weight in block) + '\n]\n\n'
        text += f'theorem {name}_valid : {name}.all (PeriodicCellRow.valid 131072) = true := by\n  decide +kernel\n\n'
        text += 'end\nend ErdosOverlap.FrontierData\n'
        (cert / f'FrontierPeriodic{chunk:03d}.lean').write_text(text)

    trig = (cert / 'Native6TrigData.lean').read_text()
    # The original list is stored as chunks in this one source file.
    original_terms = [(F(freq), F(weight)) for freq, weight in re.findall(r'⟨\(([^)]+)\), \(([^)]+)\)⟩', trig)]
    assert len(original_terms) == 641
    terms = [(freq, weight + delta.get(f'cos:{index}', F(0)))
             for index, (freq, weight) in enumerate(original_terms)]
    assert all(weight <= 0 for freq, weight in terms)
    corrections = [(freq, delta[f'cos:{index}']) for index, (freq, weight) in enumerate(original_terms)
                   if delta.get(f'cos:{index}', F(0))]
    assert len(corrections) == 32
    text = header(['ErdosOverlap.Numerics.SincEnclosure', 'ErdosOverlap.Certificate.Native6TrigData'],
                  'ErdosOverlap.FrontierTrig', source_hash)
    trig_names = []
    for index, start in enumerate(range(0, len(terms), 64)):
        name = f'chunk{index:02d}'
        trig_names.append(name)
        text += f'def {name} : List Numerics.CosineTerm := [\n'
        text += ',\n'.join(f'  ⟨{rat(freq)}, {rat(weight)}⟩' for freq, weight in terms[start:start+64]) + '\n]\n\n'
    text += 'def terms : List Numerics.CosineTerm :=\n  ' + ' ++\n  '.join(trig_names) + '\n\n'
    text += '''theorem allNonpositive_checked :
    terms.all (fun term => decide (term.weight ≤ 0 ∧ 0 < term.frequency)) = true := by
  decide +kernel

'''
    text += 'def correctionTerms : List Numerics.CosineTerm := [\n'
    text += ',\n'.join(f'  ⟨{rat(freq)}, {rat(weight)}⟩' for freq, weight in corrections) + '\n]\n\n'
    # Structural equality is computed once, rather than repeatedly expanding
    # a large kernel identity in downstream modules.
    indices = [index for index in range(len(original_terms)) if delta.get(f'cos:{index}', F(0))]
    text += 'def correctionIndices : List ℕ := [' + ', '.join(map(str, indices)) + ']\n\n'
    text += 'end\nend ErdosOverlap.FrontierTrig\n'
    (cert / 'FrontierTrigData.lean').write_text(text)

    native = (cert / 'Native6KernelData.lean').read_text()
    old_y0 = F(re.search(r'def y0 : ℚ := \(([^)]+)\)', native)[1])
    old_y2 = F(re.search(r'def y2 : ℚ := \(([^)]+)\)', native)[1])
    y0, y2 = old_y0 + delta.get('constant', F(0)), old_y2 + delta.get('square', F(0))
    assert y2 <= 0
    phases = [(int(index), F(multiplier), F(lower), F(mean)) for index, cells, multiplier, gamma, lower, mean in re.findall(
        r'def phase(\d+) : PhaseFunctionalRow :=\s*⟨(\d+), \(([^)]+)\), #\[(.*?)\], \(([^)]+)\), \(([^)]+)\)⟩', native, re.S)]
    assert len(phases) == 23
    multipliers = [old + delta.get(f'phase:{index}', F(0)) for index, old, lower, mean in phases]
    assert all(x >= 0 for x in multipliers)
    rational_part = y0 + y2*F(2, 3) + sum((2*w if per else F(0)) for r, k, cell, per, w in net_rows)
    rational_part += sum(multiplier*lower for multiplier, (index, old, lower, mean) in zip(multipliers, phases))
    mean_coefficient = y2/2 + sum(multiplier*mean for multiplier, (index, old, lower, mean) in zip(multipliers, phases))
    assert mean_coefficient == F(data['mean_coefficient'])
    imports = ['ErdosOverlap.Certificate.Native6KernelData'] + [f'ErdosOverlap.Certificate.FrontierPeriodic{i:03d}' for i in range(len(periodic_names))]
    text = header(imports, 'ErdosOverlap.FrontierData', source_hash)
    text += f'def y0 : ℚ := {rat(y0)}\ndef y2 : ℚ := {rat(y2)}\n\n'
    text += 'theorem y2_nonpositive : y2 ≤ 0 := by decide +kernel\n\n'
    text += 'def periodicRows : List PeriodicCellRow :=\n  ' + ' ++\n  '.join(periodic_names) + '\n\n'
    text += '''theorem periodicRows_valid :
    periodicRows.all (PeriodicCellRow.valid Native6Data.cells) = true := by
  simp only [periodicRows, Native6Data.cells, List.all_append,
    ''' + ', '.join(name+'_valid' for name in periodic_names) + ''', Bool.and_self]

'''
    for (index, old, lower, mean), multiplier in zip(phases, multipliers):
        text += f'def phase{index:02d} : PhaseFunctionalRow :=\n  {{ Native6Data.phase{index:02d} with multiplier := {rat(multiplier)} }}\n\n'
    text += 'def phaseRows : List PhaseFunctionalRow := [' + ', '.join(f'phase{i:02d}' for i in range(23)) + ']\n\n'
    text += 'theorem phaseRows_valid : phaseRows.all PhaseFunctionalRow.valid = true := by\n  decide +kernel\n\n'
    text += f'def rationalPartExact : ℚ := {rat(rational_part)}\n\n'
    text += f'def meanCoefficientExact : ℚ := {rat(mean_coefficient)}\n\n'
    text += '''theorem algebraic_part_checked :
    y0 + y2 * (2 / 3) + periodicRowsLower periodicRows +
      phaseRowsLower phaseRows = rationalPartExact := by
  decide +kernel

theorem mean_coefficient_checked :
    y2 / 2 + phaseRowsMeanCoefficient phaseRows = meanCoefficientExact := by
  decide +kernel

theorem meanCoefficient_nonpositive : meanCoefficientExact ≤ 0 := by
  decide +kernel

end
end ErdosOverlap.FrontierData
'''
    (cert / 'FrontierKernelData.lean').write_text(text)
    print(json.dumps({'kernel_sha256': source_hash, 'periodic_rows': len(net_rows),
                      'cosine_terms': len(terms), 'cosine_corrections': len(corrections),
                      'rational_part': str(rational_part), 'mean_coefficient': str(mean_coefficient)}, indent=2))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--package', type=Path, default=Path(__file__).resolve().parent.parent)
    generate(parser.parse_args().package)
