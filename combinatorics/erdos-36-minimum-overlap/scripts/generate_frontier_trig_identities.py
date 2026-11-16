"""Generate small algebraic source identities for the sparse cosine correction."""
import argparse
from fractions import Fraction as F
import json
from pathlib import Path
import re


def rat(q):
    q = F(q)
    return f'({q.numerator} / {q.denominator} : ℚ)'


def generate(package):
    cert = package / 'ErdosOverlap/Certificate'
    original = [(F(freq), F(weight)) for freq, weight in re.findall(
        r'⟨\(([^)]+)\), \(([^)]+)\)⟩', (cert/'Native6TrigData.lean').read_text())]
    frozen = json.loads((package/'certificates/frontier/kernel.json').read_text())
    delta = {key: F(q) for key, q in frozen['delta'].items()}
    text = '''/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.FrontierTrigData

namespace ErdosOverlap.FrontierTrig
open Numerics
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem cosineSum_append (xs ys : List CosineTerm) (t : ℝ) :
    cosineSum (xs ++ ys) t = cosineSum xs t + cosineSum ys t := by
  induction xs with
  | nil => simp [cosineSum]
  | cons x xs ih => simp only [List.cons_append, cosineSum, ih]; ring

'''
    names = []
    for chunk, start in enumerate(range(0, len(original), 64)):
        name = f'correctionChunk{chunk:02d}'
        names.append(name)
        terms = [(original[i][0], delta[f'cos:{i}']) for i in range(start, min(start+64, len(original)))
                 if delta.get(f'cos:{i}', F(0))]
        text += f'def {name} : List CosineTerm := [' + ', '.join(f'⟨{rat(freq)}, {rat(weight)}⟩' for freq, weight in terms) + ']\n\n'
        for lemma, function in [('sum', 'cosineSum'), ('lower', 'Native6.cosineLower')]:
            argument = ' (t : ℝ)' if lemma == 'sum' else ''
            suffix = ' t' if lemma == 'sum' else ''
            text += f'''theorem chunk{chunk:02d}_{lemma}_identity{argument} :
    {function} chunk{chunk:02d}{suffix} =
      {function} Native6Trig.chunk{chunk:02d}{suffix} + {function} {name}{suffix} := by
  simp only [chunk{chunk:02d}, Native6Trig.chunk{chunk:02d}, {name},
    {function}, CosineTerm.value]
  push_cast
  ring

'''
    text += 'theorem correctionTerms_split : correctionTerms =\n  ' + ' ++\n  '.join(names) + ' := by\n  rfl\n\n'
    for lemma, function, append in [('sum', 'cosineSum', 'cosineSum_append'),
                                    ('lower', 'Native6.cosineLower', 'Numerics.cosineLower_append')]:
        argument = ' (t : ℝ)' if lemma == 'sum' else ''
        suffix = ' t' if lemma == 'sum' else ''
        text += f'''theorem {lemma}_eq_old_add_corrections{argument} :
    {function} terms{suffix} = {function} Native6Trig.terms{suffix} +
      {function} correctionTerms{suffix} := by
  rw [correctionTerms_split]
  unfold terms Native6Trig.terms
  simp only [{append}]
  rw [''' + ', '.join(f'chunk{i:02d}_{lemma}_identity' for i in range(11)) + ''']
  ring

'''
    text += 'end\nend ErdosOverlap.FrontierTrig\n'
    (cert/'FrontierTrigIdentities.lean').write_text(text)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--package', type=Path, default=Path(__file__).resolve().parent.parent)
    generate(p.parse_args().package)
