"""Generate a short rational normalization bound and signed-sinc check."""
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
    frozen = json.loads((package/'certificates/frontier/kernel.json').read_text())
    raw = F(frozen['lower_at_zero'])
    bound = F((raw*10**15).numerator//(raw*10**15).denominator, 10**15)
    def read_part(path):
        return F(re.search(r'def rationalPartExact : ℚ := \(([^:]+) : ℚ\)', path.read_text())[1].replace(' ', ''))
    old = read_part(cert/'Native6Normalization.lean')
    new = read_part(cert/'FrontierKernelData.lean')
    old_bound = F(99999999999999, 10**14)
    correction = bound-old_bound-(new-old)
    text = f'''/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.FrontierKernel
public import ErdosOverlap.Certificate.FrontierTrigIdentities
public import ErdosOverlap.Certificate.Native6Grid.SincChecks

namespace ErdosOverlap.Frontier
open Numerics
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def lowerAtZeroBound : ℚ := {rat(bound)}
def sincCorrectionLower : ℚ := {rat(correction)}

theorem sinc_correction_checked :
    (sincSumBox FrontierTrig.correctionTerms).lowerBoundedBy sincCorrectionLower = true := by
  decide +kernel

theorem normalization_identity : lowerAtZeroBound =
    Native6Grid.checkedLowerAtZero +
      (FrontierData.rationalPartExact - Native6.rationalPartExact) + sincCorrectionLower := by
  decide +kernel

theorem lowerAtZeroBound_le : (lowerAtZeroBound : ℝ) ≤ lowerAtZero := by
  have hold := Native6Grid.lowerAtZero_checked
  have hcorrection := sincSum_lower_of_check _ _ sinc_correction_checked
  rw [Native6.lowerAtZero_decomposition] at hold
  have hid : (lowerAtZeroBound : ℝ) = (Native6Grid.checkedLowerAtZero : ℝ) +
      ((FrontierData.rationalPartExact : ℝ) - (Native6.rationalPartExact : ℝ)) +
      (sincCorrectionLower : ℝ) := by
    exact_mod_cast normalization_identity
  rw [hid, lowerAtZero, FrontierTrig.lower_eq_old_add_corrections]
  linarith

end
end ErdosOverlap.Frontier
'''
    (package/'ErdosOverlap/FrontierNormalization.lean').write_text(text)
    print('Short normalization lower bound:', bound, float(bound))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--package', type=Path, default=Path(__file__).resolve().parent.parent)
    generate(p.parse_args().package)
