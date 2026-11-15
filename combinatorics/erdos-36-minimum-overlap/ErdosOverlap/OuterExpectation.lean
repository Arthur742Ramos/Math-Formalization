/-
Copyright (c) 2026. Released under the BSD-3-Clause license.
-/
module

public import ErdosOverlap.Certificate.OuterData
public import ErdosOverlap.Certificate.OuterFrequencyBounds

/-!
# Unconditional physical inequalities for all 180 outer kernels

All feature RHS bounds, multiplier signs, and source-to-polynomial
identities have been discharged. Only the subsequent numerical integral
upper bounds are supplied to the final numerical assembly theorem.
-/

namespace ErdosOverlap.Outer180
open MeasureTheory Set
public section
noncomputable section

theorem bin_checked {b : OuterBinData} (hb : b ∈ bins) : b.check frequencies = true :=
  List.all_eq_true.mp bins_checked b hb

theorem bin_expectation {h : ℝ → ℝ} (hh : Admissible h)
    (b : OuterBinData) (hb : b ∈ bins)
    (hm : profileMean (overlapProfile h) ∈ Icc (b.lo : ℝ) (b.hi : ℝ)) :
    1 ≤ squarePairing h b.kernel :=
  b.expectation hh hm frequencies frequencies_valid (bin_checked hb)

/-- Every selected outer kernel satisfies the actual physical cap
inequality; this is independent of any stored numerical denominator. -/
theorem bin_cap_bound {h : ℝ → ℝ} {M : ℝ} (hh : Admissible h)
    (hcap : OverlapCap h M) (b : OuterBinData) (hb : b ∈ bins)
    (hm : profileMean (overlapProfile h) ∈ Icc (b.lo : ℝ) (b.hi : ℝ)) :
    1 ≤ M * signedKernelDenominator b.kernel :=
  b.cap_bound hh hcap hm frequencies frequencies_valid (bin_checked hb)

/-- Bridge from an exact polynomial integral enclosure to the physical
mean-row inequality used by the cover. -/
theorem bin_numerical_bound {h : ℝ → ℝ} {M : ℝ} (hh : Admissible h)
    (hcap : OverlapCap h M) (b : OuterBinData) (hb : b ∈ bins)
    (hm : profileMean (overlapProfile h) ∈ Icc (b.lo : ℝ) (b.hi : ℝ))
    (p : OuterFourierPolynomial) (hp : p = b.compile) (D : ℚ)
    (hD : (∫ t in (-2 : ℝ)..2, max (p.value t) 0) ≤ (D : ℝ)) :
    1 ≤ M * (D : ℝ) := by
  have heq : p.value = b.kernel := by
    funext t
    rw [hp, b.compile_value]
  rw [heq] at hD
  exact (bin_cap_bound hh hcap b hb hm).trans
    (mul_le_mul_of_nonneg_left hD (hcap.nonneg hh))

end
end
end ErdosOverlap.Outer180
