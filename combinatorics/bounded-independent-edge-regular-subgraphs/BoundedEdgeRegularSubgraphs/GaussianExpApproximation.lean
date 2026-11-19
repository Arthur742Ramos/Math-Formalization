module

public import BoundedEdgeRegularSubgraphs.GaussianConcentration
import Mathlib.Analysis.Convex.Integral
import Mathlib.Tactic

/-!
# Gaussian concentration of the exponential of a bounded function
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace BoundedEdgeRegularSubgraphs

/-- The (L^2) estimate used for the clipped quartic in Lemma A.3. -/
theorem integral_sq_exp_sub_exp_mean_le {n : ℕ} (hn : 0 < n)
    (H : EuclideanSpace ℝ (Fin n) → ℝ) (K : ℝ≥0) (hH : LipschitzWith K H)
    {B : ℝ} (hB : ∀ x, |H x| ≤ B) :
    let γ := stdGaussian (EuclideanSpace ℝ (Fin n))
    let m := ∫ x, H x ∂γ
    (∫ x, (Real.exp (H x) - Real.exp m) ^ 2 ∂γ) ≤
      Real.exp (2 * m) * (Real.exp (2 * (K : ℝ) ^ 2) - 1) := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin n))
  let m := ∫ x, H x ∂γ
  have hHi : Integrable H γ := Integrable.of_bound hH.continuous.aestronglyMeasurable B
    (ae_of_all _ (fun x ↦ by simpa only [Real.norm_eq_abs] using hB x))
  have hEi (s : ℝ) (hs : 0 ≤ s) : Integrable (fun x ↦ Real.exp (s * H x)) γ :=
    Integrable.of_bound (Real.continuous_exp.comp (hH.continuous.const_mul s)).aestronglyMeasurable
      (Real.exp (s * B)) (ae_of_all _ (fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hB x)) hs)))
  have hE : Integrable (fun x ↦ Real.exp (H x)) γ := by
    simpa only [one_mul] using hEi 1 zero_le_one
  have hE2 : Integrable (fun x ↦ Real.exp (H x) ^ 2) γ := by
    convert hEi 2 (by norm_num) using 1
    funext x
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hJ : Real.exp m ≤ ∫ x, Real.exp (H x) ∂γ :=
    convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
      (ae_of_all _ (fun _ ↦ Set.mem_univ _)) hHi hE
  have h := integral_exp_standardGaussian_lipschitz_le hn H K hH 2
  change (∫ x, Real.exp (2 * H x) ∂γ) ≤ Real.exp (2 * m + 2 ^ 2 * (K : ℝ) ^ 2 / 2) at h
  have h₂ (x : EuclideanSpace ℝ (Fin n)) : Real.exp (H x) ^ 2 = Real.exp (2 * H x) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hm : Real.exp m ^ 2 = Real.exp (2 * m) := by
    rw [pow_two, ← Real.exp_add, two_mul]
  have he (x : EuclideanSpace ℝ (Fin n)) : (Real.exp (H x) - Real.exp m) ^ 2 =
      (Real.exp (H x) ^ 2 - (2 * Real.exp m) * Real.exp (H x)) + Real.exp m ^ 2 := by ring
  change (∫ x, (Real.exp (H x) - Real.exp m) ^ 2 ∂γ) ≤
    Real.exp (2 * m) * (Real.exp (2 * (K : ℝ) ^ 2) - 1)
  simp_rw [he]
  let g (x : EuclideanSpace ℝ (Fin n)) := Real.exp (H x) ^ 2 - (2 * Real.exp m) * Real.exp (H x)
  have hg : Integrable g γ := hE2.sub (hE.const_mul _)
  change (∫ x, g x + Real.exp m ^ 2 ∂γ) ≤ _
  rw [integral_add hg (integrable_const (Real.exp m ^ 2))]
  have hgi : (∫ x, g x ∂γ) = (∫ x, Real.exp (H x) ^ 2 ∂γ) -
      (2 * Real.exp m) * (∫ x, Real.exp (H x) ∂γ) := by
    calc
      _ = (∫ x, Real.exp (H x) ^ 2 ∂γ) - (∫ x, (2 * Real.exp m) * Real.exp (H x) ∂γ) :=
        integral_sub hE2 (hE.const_mul _)
      _ = _ := by rw [integral_const_mul]
  rw [hgi, integral_const, probReal_univ, one_smul]
  simp_rw [h₂]
  rw [show (2 : ℝ) ^ 2 * (K : ℝ) ^ 2 / 2 = 2 * (K : ℝ) ^ 2 by ring, Real.exp_add] at h
  have hb := mul_le_mul_of_nonneg_left hJ (show 0 ≤ 2 * Real.exp m by positivity)
  calc
    _ ≤ Real.exp (2 * m) * Real.exp (2 * (K : ℝ) ^ 2) - (2 * Real.exp m) * Real.exp m +
        Real.exp m ^ 2 := by linarith only [h, hb]
    _ = _ := by rw [← hm]; ring

end BoundedEdgeRegularSubgraphs
