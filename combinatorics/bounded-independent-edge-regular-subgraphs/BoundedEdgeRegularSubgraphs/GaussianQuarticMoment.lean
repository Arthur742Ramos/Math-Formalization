module

public import BoundedEdgeRegularSubgraphs.GaussianCubicMoment
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

/-!
# Second moment of the Gaussian quartic
-/

public section

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

/-- The eighth Gaussian moment gives the second-moment bound needed
for the quartic correction in Lemma A.3. -/
theorem integral_sq_gaussian_quartic_le {n : ℕ} {ι : Type*}
    (A : Finset ι) (b : ι → ℝ) (v : ι → Fin n → ℝ) :
    (∫ x, (∑ e ∈ A, b e * (v e ⬝ᵥ x) ^ 4) ^ 2 ∂standardGaussianProduct n) ≤
      105 * (A.card : ℝ) * ∑ e ∈ A, b e ^ 2 * (∑ i, v e i ^ 2) ^ 4 := by
  let γ := standardGaussianProduct n
  let f (e : ι) (x : Fin n → ℝ) := b e * (v e ⬝ᵥ x) ^ 4
  let Y (e : ι) : MvPolynomial (Fin n) ℝ := MvPolynomial.C (b e) * linearPolynomial (v e) ^ 4
  have hY (e : ι) (x : Fin n → ℝ) : MvPolynomial.eval x (Y e) = f e x := by
    simp only [Y, f, map_mul, map_pow, MvPolynomial.eval_C, eval_linearPolynomial]
  have hLeft : Integrable (fun x ↦ (∑ e ∈ A, f e x) ^ 2) γ := by
    have h (x : Fin n → ℝ) :
        MvPolynomial.eval x ((∑ e ∈ A, Y e) ^ 2) = (∑ e ∈ A, f e x) ^ 2 := by
      simp only [map_pow, map_sum, hY]
    rw [← funext h]
    exact integrable_eval_standardGaussianProduct _
  have hRight (e : ι) (_ : e ∈ A) : Integrable (fun x ↦ (f e x) ^ 2) γ := by
    have h (x : Fin n → ℝ) : MvPolynomial.eval x (Y e ^ 2) = (f e x) ^ 2 := by
      simp only [map_pow, hY]
    rw [← funext h]
    exact integrable_eval_standardGaussianProduct _
  have hp (x : Fin n → ℝ) : (∑ e ∈ A, f e x) ^ 2 ≤ (A.card : ℝ) * ∑ e ∈ A, f e x ^ 2 :=
    sq_sum_le_card_mul_sum_sq (s := A) (f := fun e ↦ f e x)
  change (∫ x, (∑ e ∈ A, f e x) ^ 2 ∂γ) ≤ _
  refine (integral_mono hLeft ((integrable_finsetSum _ hRight).const_mul _) hp).trans_eq ?_
  rw [integral_const_mul, integral_finsetSum _ hRight]
  have hM (e : ι) : (∫ x, f e x ^ 2 ∂γ) =
      b e ^ 2 * (105 * (∑ i, v e i ^ 2) ^ 4) := by
    have hpow (x : Fin n → ℝ) : f e x ^ 2 = b e ^ 2 * (v e ⬝ᵥ x) ^ 8 := by
      dsimp only [f]
      ring
    simp_rw [hpow]
    rw [integral_const_mul]
    congr 1
    have h := integral_even_pow_dotProduct_standardGaussianProduct (v e) 4
    norm_num [Finset.prod_range_succ] at h
    linarith only [h]
  simp_rw [hM]
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun e _ ↦ by ring)

end BoundedEdgeRegularSubgraphs
