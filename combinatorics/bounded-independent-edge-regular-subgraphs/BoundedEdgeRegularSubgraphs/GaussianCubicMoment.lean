module

public import BoundedEdgeRegularSubgraphs.GaussianMvPolynomial
public import BoundedEdgeRegularSubgraphs.GaussianLinearMoments
public import BoundedEdgeRegularSubgraphs.GaussianEdgeCovariance
import Mathlib.Tactic

/-!
# The bounded second moment of the Gaussian cubic correction
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

noncomputable def linearPolynomial {n : ℕ} (v : Fin n → ℝ) :
    MvPolynomial (Fin n) ℝ :=
  ∑ i, MvPolynomial.C (v i) * MvPolynomial.X i

theorem eval_linearPolynomial {n : ℕ} (v x : Fin n → ℝ) :
    MvPolynomial.eval x (linearPolynomial v) = v ⬝ᵥ x := by
  simp only [linearPolynomial, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, dotProduct]

private theorem pderiv_linearPolynomial {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    MvPolynomial.pderiv i (linearPolynomial v) = MvPolynomial.C (v i) := by
  classical
  unfold linearPolynomial
  simp [map_sum, MvPolynomial.pderiv_X, Pi.single_apply]

/-- The cubic polynomial from a finite family of Gaussian edge forms. -/
noncomputable def gaussianCubicPolynomial {n : ℕ} {ι : Type*}
    (A : Finset ι) (a : ι → ℝ) (v : ι → Fin n → ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ e ∈ A, MvPolynomial.C (a e) * linearPolynomial (v e) ^ 3

theorem eval_gaussianCubicPolynomial {n : ℕ} {ι : Type*}
    (A : Finset ι) (a : ι → ℝ) (v : ι → Fin n → ℝ) (x : Fin n → ℝ) :
    MvPolynomial.eval x (gaussianCubicPolynomial A a v) =
      ∑ e ∈ A, a e * (v e ⬝ᵥ x) ^ 3 := by
  simp only [gaussianCubicPolynomial, map_sum, map_mul, MvPolynomial.eval_C, map_pow, eval_linearPolynomial]

theorem eval_pderiv_gaussianCubicPolynomial {n : ℕ} {ι : Type*}
    (A : Finset ι) (a : ι → ℝ) (v : ι → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin n) :
    MvPolynomial.eval x (MvPolynomial.pderiv i (gaussianCubicPolynomial A a v)) =
      ∑ e ∈ A, (3 * a e * (v e ⬝ᵥ x) ^ 2) * v e i := by
  simp only [gaussianCubicPolynomial, map_sum, MvPolynomial.pderiv_C_mul]
  apply Finset.sum_congr rfl
  intro e _
  norm_num only [MvPolynomial.pderiv_pow, pderiv_linearPolynomial, map_mul, MvPolynomial.eval_C,
    map_pow, map_ofNat, eval_linearPolynomial, Nat.reduceSub]
  ring

/-- Part of Lemma A.2. The second moment of the Gaussian cubic is bounded
by the lower frame weight and the fourth moments of the linear forms. -/
theorem integral_sq_gaussianCubicPolynomial_le {n : ℕ} {ι : Type*}
    (A : Finset ι) (a w : ι → ℝ) (v : ι → Fin n → ℝ) {lower : ℝ} (hlower : 0 < lower)
    (hw : ∀ e ∈ A, lower ≤ w e)
    (hframe : ∀ x : Fin n → ℝ, (∑ e ∈ A, w e * (x ⬝ᵥ v e) ^ 2) = ∑ i, x i ^ 2) :
    (∫ x, MvPolynomial.eval x (gaussianCubicPolynomial A a v) ^ 2 ∂standardGaussianProduct n) ≤
      27 * lower⁻¹ * ∑ e ∈ A, a e ^ 2 * (∑ i, v e i ^ 2) ^ 2 := by
  let γ := standardGaussianProduct n
  let P := gaussianCubicPolynomial A a v
  let F (x : Fin n → ℝ) := MvPolynomial.eval x P
  let D (i : Fin n) (x : Fin n → ℝ) := MvPolynomial.eval x (MvPolynomial.pderiv i P)
  let Y (e : ι) (x : Fin n → ℝ) := v e ⬝ᵥ x
  have hFint : Integrable F γ := integrable_eval_standardGaussianProduct P
  have hFo : Function.Odd F := by
    intro x
    simp only [F, P, eval_gaussianCubicPolynomial, dotProduct_neg, (by decide : Odd (3 : ℕ)).neg_pow,
      mul_neg, Finset.sum_neg_distrib]
  have hmean : (∫ x, F x ∂γ) = 0 := integral_odd_standardGaussianProduct F hFint hFo
  have hDint (i : Fin n) : Integrable (fun x ↦ D i x ^ 2) γ := by
    have hh : (fun x : Fin n → ℝ ↦ MvPolynomial.eval x ((MvPolynomial.pderiv i P) ^ 2)) =
        (fun x ↦ D i x ^ 2) := funext (fun x ↦ map_pow (MvPolynomial.eval x) _ _)
    rw [← hh]
    exact integrable_eval_standardGaussianProduct _
  have hYi (e : ι) : Integrable (fun x ↦ Y e x ^ 4) γ := by
    have he : (fun x : Fin n → ℝ ↦ MvPolynomial.eval x (linearPolynomial (v e) ^ 4)) =
        (fun x ↦ Y e x ^ 4) := by
      funext x
      rw [map_pow, eval_linearPolynomial]
    rw [← he]
    exact integrable_eval_standardGaussianProduct _
  have hvar : (∫ x, F x ^ 2 ∂γ) ≤ ∑ i, ∫ x, D i x ^ 2 ∂γ := by
    have h := variance_mvPolynomial_standardGaussianProduct_le P
    change Var[F; γ] ≤ _ at h
    rw [variance_eq_integral hFint.aemeasurable, hmean] at h
    simpa only [sub_zero] using h
  have hpoint (x : Fin n → ℝ) : (∑ i, D i x ^ 2) ≤
      lower⁻¹ * ∑ e ∈ A, (9 * a e ^ 2) * Y e x ^ 4 := by
    change (∑ i, (MvPolynomial.eval x (MvPolynomial.pderiv i P)) ^ 2) ≤ _
    simp_rw [P, eval_pderiv_gaussianCubicPolynomial]
    have heq (e : ι) : (3 * a e * Y e x ^ 2) ^ 2 = (9 * a e ^ 2) * Y e x ^ 4 := by ring
    have h := weighted_frame_synthesis_le A v w (fun e ↦ 3 * a e * Y e x ^ 2)
      hlower hw hframe
    simpa only [heq] using h
  refine hvar.trans ?_
  rw [← integral_finsetSum _ (fun i _ ↦ hDint i)]
  have hI (e : ι) (_ : e ∈ A) : Integrable (fun x ↦ (9 * a e ^ 2) * Y e x ^ 4) γ :=
    (hYi e).const_mul _
  calc
    _ ≤ ∫ x, lower⁻¹ * ∑ e ∈ A, (9 * a e ^ 2) * Y e x ^ 4 ∂γ :=
      integral_mono (integrable_finsetSum _ (fun i _ ↦ hDint i))
        ((integrable_finsetSum A hI).const_mul _) hpoint
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum _ hI]
      simp_rw [integral_const_mul]
      have he (e : ι) : (∫ x, Y e x ^ 4 ∂γ) = 3 * (∑ i, v e i ^ 2) ^ 2 := by
        have h := integral_even_pow_dotProduct_standardGaussianProduct (v e) 2
        norm_num [Finset.prod_range_succ] at h
        change _ = _
        linarith only [h]
      simp_rw [he]
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      ring

end BoundedEdgeRegularSubgraphs
