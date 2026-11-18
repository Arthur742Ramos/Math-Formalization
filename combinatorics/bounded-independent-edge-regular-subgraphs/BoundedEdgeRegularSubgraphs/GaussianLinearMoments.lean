module

public import BoundedEdgeRegularSubgraphs.GaussianProductParts
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Tactic

/-!
# Gaussian moments of linear forms
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators NNReal

namespace BoundedEdgeRegularSubgraphs

/-- Passing from product coordinates to Euclidean space gives the standard
Gaussian law of Mathlib. -/
theorem map_standardGaussianProduct_toLp (n : ℕ) :
    (standardGaussianProduct n).map (WithLp.toLp 2) =
      stdGaussian (EuclideanSpace ℝ (Fin n)) :=
  map_pi_eq_stdGaussian

/-- A linear form has variance equal to the sum of the squares of its
coefficients. -/
theorem map_standardGaussianProduct_dotProduct {n : ℕ} (v : Fin n → ℝ) :
    (standardGaussianProduct n).map (fun x ↦ v ⬝ᵥ x) =
      gaussianReal 0 ⟨∑ i, v i ^ 2, Finset.sum_nonneg (fun i _ ↦ sq_nonneg (v i))⟩ := by
  let E := EuclideanSpace ℝ (Fin n)
  let w : E := WithLp.toLp 2 v
  let L : StrongDual ℝ E := innerSL ℝ w
  have hL (x : Fin n → ℝ) : L (WithLp.toLp 2 x) = v ⬝ᵥ x := by
    change inner ℝ (WithLp.toLp 2 v) (WithLp.toLp 2 x) = v ⬝ᵥ x
    rw [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm]
  have hm : Measurable (WithLp.toLp (V := Fin n → ℝ) 2) :=
    (EuclideanSpace.equiv (Fin n) ℝ).symm.continuous.measurable
  have hmap : (standardGaussianProduct n).map (fun x ↦ v ⬝ᵥ x) =
      (stdGaussian E).map L := by
    rw [← map_standardGaussianProduct_toLp, Measure.map_map L.continuous.measurable hm]
    congr 1
    funext x
    exact (hL x).symm
  rw [hmap, IsGaussian.map_eq_gaussianReal]
  have hμ : (∫ x, L x ∂stdGaussian E) = 0 := by
    exact integral_strongDual_stdGaussian L
  have hv : ‖L‖ ^ 2 = ∑ i, v i ^ 2 := by
    rw [show ‖L‖ = ‖w‖ from innerSL_apply_norm ℝ w, EuclideanSpace.real_norm_sq_eq]
  rw [hμ, variance_dual_stdGaussian, hv]
  exact congrArg (gaussianReal 0) (Real.toNNReal_of_nonneg
    (Finset.sum_nonneg fun i _ ↦ sq_nonneg (v i)))

/-- The even moments in Appendix A for a linear form of the standard
Gaussian product. -/
theorem integral_even_pow_dotProduct_standardGaussianProduct {n : ℕ} (v : Fin n → ℝ) (m : ℕ) :
    (∫ x, (v ⬝ᵥ x) ^ (2 * m) ∂standardGaussianProduct n) =
      (∑ i, v i ^ 2) ^ m * ∏ j ∈ Finset.range m, (2 * (j : ℝ) + 1) := by
  have hm : Measurable (fun x ↦ v ⬝ᵥ x) := by
    unfold dotProduct
    exact Finset.measurable_sum _ (fun i _ ↦ measurable_const.mul (measurable_pi_apply i))
  let w : ℝ≥0 := ⟨∑ i, v i ^ 2, Finset.sum_nonneg (fun i _ ↦ sq_nonneg (v i))⟩
  have h := integral_map (μ := standardGaussianProduct n) hm.aemeasurable
    ((continuous_id.pow (2 * m)).measurable.aestronglyMeasurable :
      AEStronglyMeasurable (fun u : ℝ ↦ u ^ (2 * m))
        ((standardGaussianProduct n).map (fun x ↦ v ⬝ᵥ x)))
  rw [map_standardGaussianProduct_dotProduct] at h
  exact h.symm.trans (integral_even_pow_gaussianReal w m)

/-- Simultaneous negation of all standard Gaussian coordinates preserves
their joint law. -/
theorem measurePreserving_neg_standardGaussianProduct (n : ℕ) :
    MeasurePreserving (fun x : Fin n → ℝ ↦ -x)
      (standardGaussianProduct n) (standardGaussianProduct n) := by
  unfold standardGaussianProduct
  refine measurePreserving_pi _ _ (fun _ ↦ ⟨measurable_neg, ?_⟩)
  change (gaussianReal 0 1).map (fun x : ℝ ↦ -x) = gaussianReal 0 1
  rw [gaussianReal_map_neg, neg_zero]

/-- Odd functions of the standard Gaussian product have zero mean. -/
theorem integral_odd_standardGaussianProduct {n : ℕ} (F : (Fin n → ℝ) → ℝ)
    (hF : Integrable F (standardGaussianProduct n)) (ho : Function.Odd F) :
    (∫ x, F x ∂standardGaussianProduct n) = 0 := by
  let γ := standardGaussianProduct n
  have hp := measurePreserving_neg_standardGaussianProduct n
  have hm : AEStronglyMeasurable F (γ.map (fun x ↦ -x)) := by
    rw [hp.map_eq]
    exact hF.aestronglyMeasurable
  have h := integral_map hp.measurable.aemeasurable hm
  rw [hp.map_eq] at h
  change (∫ x, F x ∂γ) = ∫ x, F (-x) ∂γ at h
  rw [show (fun x : Fin n → ℝ ↦ F (-x)) = (fun x ↦ -F x) from funext ho, integral_neg] at h
  linarith only [h]

end BoundedEdgeRegularSubgraphs
