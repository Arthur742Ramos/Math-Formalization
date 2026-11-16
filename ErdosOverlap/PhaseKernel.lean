/-
Copyright (c) 2026. Released under the BSD-3-Clause license.
-/
module

public import ErdosOverlap.FourierKernel

/-!
# The shared exact phase-functional kernel

The zero-centered hat has coefficient `gamma[0]/a`; every positive hat
has coefficient `gamma[k]/(2*a)`. The absolute-value argument defines the
even extension. This module is shared by analytic phase bounds and the
native affine compiler.
-/

namespace ErdosOverlap

open scoped BigOperators

public section
noncomputable section

@[expose] def phaseHat (a center t : ℝ) : ℝ := max (1 - |t - center| / a) 0

@[expose] def phaseKernel (N : ℕ) (gamma : Array ℚ) (t : ℝ) : ℝ :=
  let a : ℝ := 2 / N
  (gamma.getD 0 0 : ℝ) / a * phaseHat a 0 |t| +
    ∑ k ∈ Finset.range N,
      (gamma.getD (k + 1) 0 : ℝ) / (2 * a) * phaseHat a ((k + 1 : ℕ) * a) |t|

theorem phaseKernel_even (N : ℕ) (gamma : Array ℚ) (t : ℝ) :
    phaseKernel N gamma (-t) = phaseKernel N gamma t := by
  simp only [phaseKernel, abs_neg]

theorem phaseHat_continuous (a center : ℝ) : Continuous (phaseHat a center) := by
  exact (continuous_const.sub ((continuous_abs.comp
    (continuous_id.sub continuous_const)).div_const a)).max continuous_const

theorem phaseKernel_continuous (N : ℕ) (gamma : Array ℚ) : Continuous (phaseKernel N gamma) := by
  unfold phaseKernel
  apply Continuous.add
  · exact continuous_const.mul ((phaseHat_continuous _ _).comp continuous_abs)
  · apply continuous_finsetSum
    intro k _
    exact continuous_const.mul ((phaseHat_continuous _ _).comp continuous_abs)

end
end
end ErdosOverlap
