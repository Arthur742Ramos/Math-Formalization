/-
Copyright (c) 2026. Released under the BSD-3-Clause license.
-/
module

public import ErdosOverlap.Native6Kernel

/-! # Exact algebraic normalization of the frozen native6 kernel

Only the cosine return is transcendental.  The equalities below check
all stored rational row returns against the exact kernel assembly.
Their mathematical validity as overlap returns is established separately
by the physical Fourier, periodic, and phase lemmas.
-/

namespace ErdosOverlap.Native6
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def rationalPartExact : ℚ := (899962383998508372864656690689803266746908874156905624667292376042337600501153 / 899900959004451900000000000000000000000000000000000000000000000000000000000000 : ℚ)

def meanCoefficientExact : ℚ := (-13758901883347614406750139293964374100848414065304341625412297 / 20000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem algebraicLowerAtZero_exact : algebraicLowerAtZero = rationalPartExact := by
  decide +kernel

theorem meanCoefficient_exact : meanCoefficient = meanCoefficientExact := by
  decide +kernel

theorem lowerAtZero_decomposition :
    lowerAtZero = (rationalPartExact : ℝ) + cosineLower Native6Trig.terms := by
  rw [lowerAtZero, algebraicLowerAtZero_exact]

theorem meanCoefficient_nonpos : meanCoefficient ≤ 0 := by
  rw [meanCoefficient_exact]
  decide +kernel

end
end ErdosOverlap.Native6
