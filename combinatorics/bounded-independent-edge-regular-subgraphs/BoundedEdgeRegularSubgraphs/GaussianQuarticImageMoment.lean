module

public import BoundedEdgeRegularSubgraphs.GaussianQuarticMoment
public import BoundedEdgeRegularSubgraphs.GaussianClippedMean
import Mathlib.Analysis.Convex.Integral
import Mathlib.Tactic

/-!
# Quartic moments with bounds on the coordinate variances
-/

public section

open MeasureTheory Matrix Set MvPolynomial
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

/-- If every coordinate of the Gaussian image has variance at most
`D`, the quartic has an integrable square with a bound in terms of `D`. -/
theorem gaussian_edgeQuartic_image_moments {n : ℕ} (A : Finset (Edge (Fin n)))
    (b : Edge (Fin n) → ℝ) {K D : ℝ} (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hb : ∀ e ∈ A, |b e| ≤ K) (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : ∀ i, (∑ j, (B i j) ^ 2) ≤ D) :
    let γ := standardGaussianProduct n
    let h := fun x ↦ edgeQuartic A b (B *ᵥ x)
    let W := 105 * (A.card : ℝ) ^ 2 * K ^ 2 * (4 * D) ^ 4
    Integrable h γ ∧ Integrable (fun x ↦ h x ^ 2) γ ∧
      (∫ x, h x ^ 2 ∂γ) ≤ W ∧ |∫ x, h x ∂γ| ≤ Real.sqrt W := by
  let γ := standardGaussianProduct n
  let h (x : Fin n → ℝ) := edgeQuartic A b (B *ᵥ x)
  let W := 105 * (A.card : ℝ) ^ 2 * K ^ 2 * (4 * D) ^ 4
  let v (e : Edge (Fin n)) : Fin n → ℝ := B e.val.1 + B e.val.2
  let P : MvPolynomial (Fin n) ℝ := ∑ e ∈ A, C (b e) * linearPolynomial (v e) ^ 4
  have he (x : Fin n → ℝ) : eval x P = h x := by
    simp only [P, map_sum, map_mul, map_pow, eval_C, eval_linearPolynomial,
      h, edgeQuartic, v, add_dotProduct, Matrix.mulVec_apply, Matrix.row]
  have h₁ : Integrable h γ := by
    rw [← funext he]
    exact integrable_eval_standardGaussianProduct P
  have h₂ : Integrable (fun x ↦ h x ^ 2) γ := by
    rw [show (fun x ↦ h x ^ 2) = (fun x ↦ eval x (P ^ 2)) by
      funext x
      rw [map_pow, he]]
    exact integrable_eval_standardGaussianProduct (P ^ 2)
  have hv (e : Edge (Fin n)) : (∑ j, v e j ^ 2) ≤ 4 * D := by
    have hg := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n))) (fun j _ ↦
      show v e j ^ 2 ≤ 2 * (B e.val.1 j ^ 2 + B e.val.2 j ^ 2) by
        change (B e.val.1 j + B e.val.2 j) ^ 2 ≤ _
        nlinarith only [sq_nonneg (B e.val.1 j - B e.val.2 j)])
    rw [← Finset.mul_sum, Finset.sum_add_distrib] at hg
    linarith only [hg, hB e.val.1, hB e.val.2]
  have h₃ : (∫ x, h x ^ 2 ∂γ) ≤ W := by
    have hi := integral_sq_gaussian_quartic_le A b v
    have hvh (x : Fin n → ℝ) : (∑ e ∈ A, b e * (v e ⬝ᵥ x) ^ 4) = h x := by
      simp only [h, edgeQuartic, v, add_dotProduct, Matrix.mulVec_apply, Matrix.row]
    simp_rw [hvh] at hi
    refine hi.trans ?_
    have hs : (∑ e ∈ A, b e ^ 2 * (∑ j, v e j ^ 2) ^ 4) ≤
        (A.card : ℝ) * (K ^ 2 * (4 * D) ^ 4) := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum (fun e he' ↦ mul_le_mul
        (by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hb e he') 2)
        (pow_le_pow_left₀ (Finset.sum_nonneg (fun j _ ↦ sq_nonneg (v e j))) (hv e) 4)
        (by positivity) (sq_nonneg _))
    refine (mul_le_mul_of_nonneg_left hs (by positivity)).trans_eq ?_
    dsimp only [W]
    ring
  have hm : (∫ x, |h x| ∂γ) ≤ Real.sqrt W := by
    have h₂' : Integrable (fun x ↦ |h x| ^ 2) γ := by simpa only [sq_abs] using h₂
    have hJ := (convexOn_pow (𝕜 := ℝ) 2).map_integral_le
      ((continuous_id.pow 2).continuousOn) isClosed_Ici
      (ae_of_all γ (fun x ↦ show |h x| ∈ Ici 0 from abs_nonneg _)) h₁.abs h₂'
    apply (Real.le_sqrt (integral_nonneg fun x ↦ abs_nonneg (h x)) (by dsimp only [W]; positivity)).2
    exact (by simpa only [Function.comp_apply, sq_abs] using hJ : _ ≤ ∫ x, h x ^ 2 ∂γ).trans h₃
  exact ⟨h₁, h₂, h₃, (norm_integral_le_integral_norm h).trans (by simpa only [Real.norm_eq_abs] using hm)⟩

end BoundedEdgeRegularSubgraphs
