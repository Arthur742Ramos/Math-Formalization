module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
import BoundedEdgeRegularSubgraphs.Vendor.StatsMLlib.Probability.Gaussian.LipschitzConcentrationEuclidean
import Mathlib.Tactic

/-!
# Exponential moments of Lipschitz functions of a standard Gaussian
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace BoundedEdgeRegularSubgraphs

/-- The Gaussian concentration bound in (A.1), in exponential-moment form. -/
theorem integral_exp_standardGaussian_lipschitz_le {n : ℕ} (hn : 0 < n)
    (H : EuclideanSpace ℝ (Fin n) → ℝ) (K : ℝ≥0) (hH : LipschitzWith K H) (s : ℝ) :
    let γ := stdGaussian (EuclideanSpace ℝ (Fin n))
    (∫ x, Real.exp (s * H x) ∂γ) ≤
      Real.exp (s * (∫ x, H x ∂γ) + s ^ 2 * (K : ℝ) ^ 2 / 2) := by
  change _ ≤ Real.exp (s * (∫ x, H x ∂stdGaussian (EuclideanSpace ℝ (Fin n))) +
    s ^ 2 * (K : ℝ) ^ 2 / 2)
  rw [← GaussianMeasure.stdGaussianE_eq_stdGaussian n]
  let γ := GaussianMeasure.stdGaussianE n
  have : IsProbabilityMeasure γ := GaussianMeasure.stdGaussianE_isProbabilityMeasure
  let m := ∫ x, H x ∂γ
  change (∫ x, Real.exp (s * H x) ∂γ) ≤ Real.exp (s * m + s ^ 2 * (K : ℝ) ^ 2 / 2)
  rcases eq_or_ne K 0 with hK | hK
  · have hC (x : EuclideanSpace ℝ (Fin n)) : H x = H 0 := by
      apply dist_eq_zero.mp
      have hd := hH.dist_le_mul x 0
      rw [hK, NNReal.coe_zero, zero_mul] at hd
      exact le_antisymm hd dist_nonneg
    dsimp only [m]
    simp_rw [hC]
    simp [hK, probReal_univ]
  have hpos : 0 < K := lt_of_le_of_ne K.property (Ne.symm hK)
  have hh := GaussianLipConcen.lipschitz_cgf_bound hn hpos hH s
  change cgf (fun x ↦ H x - m) γ s ≤ _ at hh
  rw [cgf, mgf] at hh
  have hi : Integrable (fun x ↦ Real.exp (s * (H x - m))) γ :=
    GaussianLipConcen.lipschitz_exp_centered_integrable_E hH s
  have h := Real.exp_le_exp.mpr hh
  rw [Real.exp_log (integral_exp_pos hi)] at h
  have he (x : EuclideanSpace ℝ (Fin n)) : Real.exp (s * H x) =
      Real.exp (s * m) * Real.exp (s * (H x - m)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [he]
  rw [integral_const_mul, Real.exp_add]
  exact mul_le_mul_of_nonneg_left h (Real.exp_nonneg _)

end BoundedEdgeRegularSubgraphs
