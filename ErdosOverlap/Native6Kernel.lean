/-
Copyright (c) 2026. Released under the BSD-3-Clause license.
-/
module

public import ErdosOverlap.Certificate.Native6KernelData
public import ErdosOverlap.Certificate.Native6TrigData

/-!
# The exact frozen native6 kernel

The coefficient inputs are rational. The function is assembled from the
physical periodic rows and the shared phase-hat definition, together with
the same cosine list used by numerical integration. Bounds on its
expectation are separate theorems; stored phase return values alone are
not assumptions establishing such a bound.
-/

namespace ErdosOverlap.Native6

public section
noncomputable section

@[expose] def kernel (t : ℝ) : ℝ :=
  (Native6Data.y0 : ℝ) + (Native6Data.y2 : ℝ) * t ^ 2 +
    Numerics.cosineSum Native6Trig.terms t +
    periodicRowsKernel Native6Data.cells Native6Data.periodicRows t +
    phaseRowsKernel Native6Data.phaseRows t

@[expose] def algebraicLowerAtZero : ℚ :=
  Native6Data.y0 + Native6Data.y2 * (2 / 3) +
    periodicRowsLower Native6Data.periodicRows + phaseRowsLower Native6Data.phaseRows

@[expose] def meanCoefficient : ℚ :=
  Native6Data.y2 / 2 + phaseRowsMeanCoefficient Native6Data.phaseRows

@[expose] def cosineLower : List Numerics.CosineTerm → ℝ
  | [] => 0
  | a :: rest => (a.weight : ℝ) * Real.sinc (a.frequency : ℝ) ^ 2 + cosineLower rest

@[expose] def lowerAtZero : ℝ := (algebraicLowerAtZero : ℝ) + cosineLower Native6Trig.terms

@[expose] def lowerExpectation (m : ℝ) : ℝ := lowerAtZero + (meanCoefficient : ℝ) * m ^ 2

end
end
end ErdosOverlap.Native6
