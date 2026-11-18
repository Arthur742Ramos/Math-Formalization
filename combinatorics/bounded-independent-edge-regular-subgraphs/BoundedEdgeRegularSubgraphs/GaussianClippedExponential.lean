module

public import BoundedEdgeRegularSubgraphs.GaussianClippedMean
public import BoundedEdgeRegularSubgraphs.GaussianLinearMoments
import Mathlib.Tactic

/-!
# Exponential moments of the clipped Fourier correction
-/

public section

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators NNReal

namespace BoundedEdgeRegularSubgraphs

/-- The explicit bound on the absolute mean, together with Gaussian
concentration, controls the total clipped quartic weight. -/
theorem integral_exp_clipped_edgeQuartic_le {n : ℕ} (hn : 0 < n)
    (A : Finset (Edge (Fin n))) (b : Edge (Fin n) → ℝ)
    {K r L D : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r) (hL : 0 ≤ L)
    (hb : ∀ e ∈ A, |b e| ≤ K) (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : ∀ v : Fin n → ℝ, (∑ i, (B *ᵥ v) i ^ 2) ≤ L ^ 2 * ∑ i, v i ^ 2)
    (hD : ∀ i, (∑ j, B i j ^ 2) ≤ D) :
    let κ := 4 * (2 * r) ^ 3 * K * ((n : ℝ) - 1) * Real.sqrt n * L
    (∫ x, Real.exp (edgeQuartic A b (fun i ↦ clipRadius r ((B *ᵥ x) i))) ∂standardGaussianProduct n) ≤
      Real.exp (24 * K * ((n : ℝ) - 1) * n * D ^ 2 + κ ^ 2 / 2) := by
  let E := EuclideanSpace ℝ (Fin n)
  let H (z : E) := edgeQuartic A b (fun i ↦ clipRadius r ((B *ᵥ WithLp.ofLp z) i))
  let H₀ (x : Fin n → ℝ) := edgeQuartic A b (fun i ↦ clipRadius r ((B *ᵥ x) i))
  let κ := 4 * (2 * r) ^ 3 * K * ((n : ℝ) - 1) * Real.sqrt n * L
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hκ : 0 ≤ κ := by
    dsimp only [κ]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr hn₁))
      (Real.sqrt_nonneg _)) hL
  have hLip : LipschitzWith (⟨κ, hκ⟩ : ℝ≥0) H := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, EuclideanSpace.dist_eq]
    simp only [Real.dist_eq, sq_abs]
    change _ ≤ κ * _
    have h := abs_edgeQuartic_clip_linear_sub_le A b hK hr hL hb B hB (WithLp.ofLp x) (WithLp.ofLp y)
    simpa only [H, κ, Fintype.card_fin, mul_assoc] using h
  have hmeas : Measurable (WithLp.toLp (V := Fin n → ℝ) 2) :=
    (EuclideanSpace.equiv (Fin n) ℝ).symm.continuous.measurable
  have htransport (f : E → ℝ) (hf : StronglyMeasurable f) :
      (∫ z, f z ∂stdGaussian E) = ∫ x, f (WithLp.toLp 2 x) ∂standardGaussianProduct n := by
    rw [← map_standardGaussianProduct_toLp]
    exact integral_map hmeas.aemeasurable hf.aestronglyMeasurable
  have hm := htransport H hLip.continuous.stronglyMeasurable
  change (∫ z, H z ∂stdGaussian E) = ∫ x, H₀ x ∂standardGaussianProduct n at hm
  have hmean := integral_abs_clipped_edgeQuartic_le hn A b hK hr hb B hD
  have hmean' : (∫ z, H z ∂stdGaussian E) ≤ 24 * K * ((n : ℝ) - 1) * n * D ^ 2 := by
    rw [hm]
    refine (le_abs_self _).trans ((norm_integral_le_integral_norm H₀).trans ?_)
    simpa only [Real.norm_eq_abs] using hmean
  have h := integral_exp_standardGaussian_lipschitz_le hn H ⟨κ, hκ⟩ hLip 1
  simp only [one_mul, one_pow] at h
  refine (htransport (fun z ↦ Real.exp (H z))
    (Real.continuous_exp.comp hLip.continuous).stronglyMeasurable).symm.le.trans (h.trans ?_)
  apply Real.exp_le_exp.mpr
  change (∫ z, H z ∂stdGaussian E) + κ ^ 2 / 2 ≤ 24 * K * ((n : ℝ) - 1) * n * D ^ 2 + κ ^ 2 / 2
  linarith only [hmean']

end BoundedEdgeRegularSubgraphs
