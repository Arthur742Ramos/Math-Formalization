/-
Copyright (c) 2026. Released under the BSD-3-Clause license.
-/
module

public import ErdosOverlap.KernelExpectation
public import ErdosOverlap.Gram.Native6Phase
public import ErdosOverlap.Certificate.Native6Normalization

/-!
# Unconditional physical expectation of the frozen native6 kernel

Every component is a theorem about actual admissible densities. The phase
premises in the general assembly lemma are discharged by the 23 exact
matrix certificates and their proved physical covariance interpretation.
-/

namespace ErdosOverlap.Native6
public section
noncomputable section

theorem lowerExpectation_le {h : ℝ → ℝ} (hh : Admissible h) :
    lowerExpectation (profileMean (overlapProfile h)) ≤ quartetFunctional h kernel :=
  lowerExpectation_le_of_phase hh (fun row hr => Gram.native6_phase_functional hh row hr)

theorem exact_lowerExpectation_le {h : ℝ → ℝ} (hh : Admissible h) :
    (rationalPartExact : ℝ) + cosineLower Native6Trig.terms +
      (meanCoefficientExact : ℝ) * profileMean (overlapProfile h)^2 ≤
        quartetFunctional h kernel := by
  have hb := lowerExpectation_le hh
  simpa only [lowerExpectation, lowerAtZero_decomposition, meanCoefficient_exact] using hb

end
end
end ErdosOverlap.Native6
