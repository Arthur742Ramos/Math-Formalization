"""Generate a 32-frequency kernel-checked rotation/Taylor correction grid.

The integer proposals are computed here; every rotation, coefficient, factor,
seed and remainder obligation is checked again by Lean's ordinary kernel.
"""
import argparse
from fractions import Fraction as F
import json
import math
from pathlib import Path
import re

S = 2**128
COEFF_SCALE = 2**60
E0 = 2*34028236692093846346338


def rat(q):
    q = F(q)
    return f'({q.numerator} / {q.denominator} : ℚ)'


def integer(n):
    return f'({n} : ℤ)'


def header(imports):
    return '''/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

''' + ''.join(f'public import {name}\n' for name in imports) + '''
namespace ErdosOverlap.FrontierGrid
open Numerics
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

'''


def end():
    return '\nend\nend ErdosOverlap.FrontierGrid\n'


def dispatch(prefix, low=0, high=64, depth=0):
    pad = '  '*depth
    if high-low == 1:
        return pad + f'exact {prefix}_chunk{low:02d} j ' + ('hj ' if prefix == 'transitions' else '') + '(by omega) (by omega)\n'
    mid = (low+high)//2
    name = f'h{mid:03d}'
    result = pad + f'by_cases {name} : j < {mid*16}\n'
    result += pad + '· ' + dispatch(prefix, low, mid, depth+1).lstrip()
    result += pad + '· ' + dispatch(prefix, mid, high, depth+1).lstrip()
    return result


def generate(package):
    cert = package / 'ErdosOverlap/Certificate'
    output = cert / 'FrontierGrid'
    output.mkdir(exist_ok=True)
    frozen = json.loads((package / 'certificates/frontier/kernel.json').read_text())
    delta = {key: F(value) for key, value in frozen['delta'].items()}
    originals = []
    pattern = r'\(⟨\(([^)]+)\), \(([^)]+)\)⟩, ⟨\((-?\d+), (-?\d+)\), \((-?\d+), (-?\d+)\)⟩\)'
    for path in sorted((cert/'Native6Grid').glob('Seeds[0-9][0-9].lean')):
        originals.extend((F(freq), F(weight), (int(a), int(b)), (int(c), int(d)))
                         for freq, weight, a, b, c, d in re.findall(pattern, path.read_text()))
    assert len(originals) == 641
    indices = [i for i in range(len(originals)) if delta.get(f'cos:{i}', F(0))]
    seeds = [(originals[i][0], delta[f'cos:{i}'], originals[i][2], originals[i][3]) for i in indices]
    assert len(seeds) == 32
    factors = []
    for k in range(20):
        fs = []
        for freq, weight, initial, step in seeds:
            value = (1 if k%4 in (0, 3) else -1)*weight*(freq/1024)**k/F(math.factorial(k))
            fs.append((value*S).numerator//(value*S).denominator)
        factors.append(fs)
    rows = []
    current = [initial for freq, weight, initial, step in seeds]
    for j in range(1024):
        rows.append(current)
        current = [((step[0]*a-step[1]*b)//S, (step[1]*a+step[0]*b)//S)
                   for (freq, weight, initial, step), (a, b) in zip(seeds, current)]
    coefficients = []
    quantum = S*S//COEFF_SCALE
    for j, row in enumerate(rows):
        ps = []
        for k, fs in enumerate(factors):
            dot = sum(f*state[k%2] for f, state in zip(fs, row))
            p = (dot+quantum//2)//quantum
            radius = E0+j*(E0+2)
            assert abs(dot-p*quantum)+sum(abs(f) for f in fs)*radius+32*S <= S*S//10**14
            ps.append(p)
        coefficients.append(ps)
    text = header(['ErdosOverlap.Numerics.TaylorGridCheck', 'ErdosOverlap.Certificate.FrontierTrigData'])
    text += 'def seeds : List (CosineTerm × RotationSeed) := [\n'
    text += ',\n'.join(f'  (⟨{rat(freq)}, {rat(weight)}⟩, ⟨({integer(initial[0])}, {integer(initial[1])}), ({integer(step[0])}, {integer(step[1])})⟩)'
                       for freq, weight, initial, step in seeds) + '\n]\n\n'
    text += '''theorem seeds_terms : seeds.map Prod.fst = FrontierTrig.correctionTerms := by
  rfl

theorem seeds_checked : rotationSeedsCheck seeds = true := by
  decide +kernel

'''
    for k, fs in enumerate(factors):
        text += f'def factors{k:02d} : List ℤ := [' + ', '.join(integer(f) for f in fs) + ']\n\n'
        text += f'''theorem factors{k:02d}_correct : FactorRowCorrect FrontierTrig.correctionTerms {k} factors{k:02d} := by
  apply factorRowCheck_sound
  decide +kernel

'''
    text += 'def factors : ℕ → List ℤ := fun k => (#[' + ', '.join(f'factors{k:02d}' for k in range(20)) + ']).getD k []\n\n'
    text += '''theorem factors_correct (k : ℕ) (hk : k < 20) :
    FactorRowCorrect FrontierTrig.correctionTerms k (factors k) := by
  interval_cases k
'''
    text += ''.join(f'  · exact factors{k:02d}_correct\n' for k in range(20))
    text += '''
theorem remainder_checked : taylorRemainderCheck FrontierTrig.correctionTerms = true := by
  decide +kernel
''' + end()
    (output/'Factors.lean').write_text(text)
    for chunk in range(64):
        text = header(['ErdosOverlap.Numerics.TaylorGridCheck'])
        for j in range(chunk*16, (chunk+1)*16):
            text += f'def row{j:04d} : List (ℤ × ℤ) := [\n'
            text += ',\n'.join(f'  ({integer(a)}, {integer(b)})' for a, b in rows[j]) + '\n]\n\n'
            text += f'def coefficients{j:04d} : List ℤ := [' + ', '.join(integer(p) for p in coefficients[j]) + ']\n\n'
        text += end()
        assert len(text.splitlines()) < 10000
        (output/f'Data{chunk:02d}.lean').write_text(text)
    text = header([f'ErdosOverlap.Certificate.FrontierGrid.Data{chunk:02d}' for chunk in range(64)])
    text += 'def stateRows : Array (List (ℤ × ℤ)) := #[\n  ' + ',\n  '.join(f'row{j:04d}' for j in range(1024)) + '\n]\n\n'
    text += 'def coefficientRows : Array (List ℤ) := #[\n  ' + ',\n  '.join(f'coefficients{j:04d}' for j in range(1024)) + '\n]\n\n'
    text += 'def stateRow (j : ℕ) : List (ℤ × ℤ) := stateRows.getD j []\n'
    text += 'def coefficientRow (j : ℕ) : List ℤ := coefficientRows.getD j []\n'
    text += end()
    (output/'Rows.lean').write_text(text)
    for chunk in range(64):
        text = header(['ErdosOverlap.Certificate.FrontierGrid.Factors', 'ErdosOverlap.Certificate.FrontierGrid.Rows'])
        lo, hi = chunk*16, (chunk+1)*16
        text += f'''theorem coefficients_chunk{chunk:02d} (j : ℕ) (hlo : {lo} ≤ j) (hhi : j < {hi}) :
    completeCoefficientRowCheck factors (stateRow j) j (coefficientRow j) = true := by
  interval_cases j <;> decide +kernel

theorem transitions_chunk{chunk:02d} (j : ℕ) (hj : j+1 < 1024)
    (hlo : {lo} ≤ j) (hhi : j < {hi}) :
    transitionRowCheck seeds (stateRow j) (stateRow (j+1)) = true := by
  have hj' : j < 1023 := by omega
  interval_cases j <;> decide +kernel
''' + end()
        (output/f'Check{chunk:02d}.lean').write_text(text)
    text = header([f'ErdosOverlap.Certificate.FrontierGrid.Check{chunk:02d}' for chunk in range(64)])
    text += '''theorem initial_checked : initialRowCheck seeds (stateRow 0) = true := by
  decide +kernel

theorem transitions_checked (j : ℕ) (hj : j+1 < 1024) :
    transitionRowCheck seeds (stateRow j) (stateRow (j+1)) = true := by
''' + dispatch('transitions', depth=1)
    text += '''
theorem coefficients_checked (j : ℕ) (hj : j < 1024) :
    completeCoefficientRowCheck factors (stateRow j) j (coefficientRow j) = true := by
''' + dispatch('coefficients', depth=1)
    text += '''
theorem stateRows_correct (j : ℕ) (hj : j < 1024) : RowCorrect seeds (stateRow j) j := by
  apply rowCorrect_of_checked_transitions seeds stateRow 1024 _ transitions_checked hj
  exact initial_checked

theorem trigRows_correct (j : ℕ) (hj : j < 1024) :
    RowTrigCorrect FrontierTrig.correctionTerms (stateRow j) j := by
  simpa only [seeds_terms] using (stateRows_correct j hj).trig seeds_checked

theorem cosine_uniform_error (j : ℕ) (hj : j < 1024) {u : ℝ} (hu : |u| ≤ 1) :
    |cosineSum FrontierTrig.correctionTerms ((taylorGridCenter j : ℝ) + (taylorGridRadius : ℝ)*u) -
      polynomialValue (quantizedCoefficients (coefficientRow j)) u| ≤
      (1 / 1000000000000 : ℝ) := by
  exact completeCoefficientRowCheck_sound factors_correct (trigRows_correct j hj)
    (coefficients_checked j hj) remainder_checked hu
''' + end()
    (output/'UniformError.lean').write_text(text)
    (package/'certificates/frontier/correction-coefficients.json').write_text(
        json.dumps(coefficients, separators=(',', ':'))+'\n')
    print(f'Generated 32-frequency correction grid: {len(rows)} checked row proposals, 20 factors each.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--package', type=Path, default=Path(__file__).resolve().parent.parent)
    generate(parser.parse_args().package)
