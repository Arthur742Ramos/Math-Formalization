module

public import BoundedEdgeRegularSubgraphs.GaussianGradientAlgebra
public import BoundedEdgeRegularSubgraphs.GaussianGradientFourthMoment
public import BoundedEdgeRegularSubgraphs.GaussianCubicApproximation
import Mathlib.Tactic

/-!
# Variance of the cubic gradient product
-/

public section

open MeasureTheory ProbabilityTheory Matrix MvPolynomial
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

/-- The frame estimate, Gaussian fourth and eighth moments, and Gaussian
Poincaré bound the variance of the gradient product in Lemma A.2. -/
theorem variance_gaussianCubic_gradientProduct_le {n : ℕ} {ι : Type*}
    (A : Finset ι) (a w : ι → ℝ) (v : ι → Fin n → ℝ) {lower K R D : ℝ}
    (hlower : 0 < lower) (hw : ∀ e ∈ A, lower ≤ w e)
    (hframe : ∀ x : Fin n → ℝ, (∑ e ∈ A, w e * (x ⬝ᵥ v e) ^ 2) = ∑ i, x i ^ 2)
    (hK : 0 ≤ K) (ha : ∀ e ∈ A, |a e| ≤ K)
    (hR : 0 ≤ R) (hcov : ∀ e ∈ A, (∑ f ∈ A, |v e ⬝ᵥ v f|) ≤ R)
    (hD : 0 ≤ D) (hvar : ∀ e ∈ A, (∑ i, v e i ^ 2) ≤ D) :
    let G := gaussianGradientProduct (gaussianCubicPolynomial A a v) (gaussianCubicAuxiliary A a v)
    Var[fun x ↦ eval x G; standardGaussianProduct n] ≤
      8640 * lower⁻¹ * K ^ 4 * R ^ 2 * A.card * D ^ 3 := by
  let γ := standardGaussianProduct n
  let G := gaussianGradientProduct (gaussianCubicPolynomial A a v) (gaussianCubicAuxiliary A a v)
  let Y (e : ι) (x : Fin n → ℝ) := v e ⬝ᵥ x
  let Q (e : ι) := ∑ i, v e i ^ 2
  let C (e f : ι) := a f * (v e ⬝ᵥ v f)
  let P (e : ι) : MvPolynomial (Fin n) ℝ :=
    ∑ f ∈ A, MvPolynomial.C (C e f) * (linearPolynomial (v f) ^ 2 + MvPolynomial.C (Q f))
  let F (e : ι) (x : Fin n → ℝ) := ∑ f ∈ A, C e f * (Y f x ^ 2 + Q f)
  let Z (e : ι) (x : Fin n → ℝ) := 12 * a e * Y e x * F e x
  let ZP (e : ι) : MvPolynomial (Fin n) ℝ := MvPolynomial.C (12 * a e) * linearPolynomial (v e) * P e
  have hP (e : ι) (x : Fin n → ℝ) : eval x (P e) = F e x := by
    simp only [P, F, Y, map_sum, map_mul, map_add, map_pow, eval_C, eval_linearPolynomial]
  have hZint (e : ι) (_ : e ∈ A) : Integrable (fun x ↦ Z e x ^ 2) γ := by
    have h (x : Fin n → ℝ) : eval x (ZP e ^ 2) = Z e x ^ 2 := by
      simp only [ZP, Y, Z, map_pow, map_mul, eval_C, eval_linearPolynomial, hP]
    rw [← funext h]
    exact integrable_eval_standardGaussianProduct _
  have hDint (i : Fin n) (_ : i ∈ (Finset.univ : Finset (Fin n))) :
      Integrable (fun x ↦ eval x (pderiv i G) ^ 2) γ := by
    have h (x : Fin n → ℝ) : eval x ((pderiv i G) ^ 2) = eval x (pderiv i G) ^ 2 := by rw [map_pow]
    rw [← funext h]
    exact integrable_eval_standardGaussianProduct _
  have hpoint (x : Fin n → ℝ) : (∑ i, eval x (pderiv i G) ^ 2) ≤
      lower⁻¹ * ∑ e ∈ A, Z e x ^ 2 := by
    simp_rw [G, eval_pderiv_gaussianCubic_gradientProduct A a v x]
    exact weighted_frame_synthesis_le A v w (fun e ↦ Z e x) hlower hw hframe
  have hI := integral_mono (integrable_finsetSum _ hDint)
    ((integrable_finsetSum A hZint).const_mul lower⁻¹) hpoint
  rw [integral_finsetSum _ hDint, integral_const_mul, integral_finsetSum _ hZint] at hI
  have hZ (e : ι) (he : e ∈ A) : (∫ x, Z e x ^ 2 ∂γ) ≤ 8640 * K ^ 4 * R ^ 2 * D ^ 3 := by
    have hYint : Integrable (fun x ↦ Y e x ^ 4) γ := by
      have heq (x : Fin n → ℝ) : eval x (linearPolynomial (v e) ^ 4) = Y e x ^ 4 := by
        rw [map_pow, eval_linearPolynomial]
      rw [← funext heq]
      exact integrable_eval_standardGaussianProduct _
    have hFint : Integrable (fun x ↦ F e x ^ 4) γ := by
      have heq (x : Fin n → ℝ) : eval x (P e ^ 4) = F e x ^ 4 := by rw [map_pow, hP]
      rw [← funext heq]
      exact integrable_eval_standardGaussianProduct _
    have hmY := integral_even_pow_dotProduct_standardGaussianProduct (v e) 2
    norm_num [Finset.prod_range_succ] at hmY
    have hY : (∫ x, Y e x ^ 4 ∂γ) ≤ 3 * D ^ 2 := by
      have h := pow_le_pow_left₀ (Finset.sum_nonneg (fun i _ ↦ sq_nonneg (v e i))) (hvar e he) 2
      change _ ≤ _
      linarith only [hmY, h]
    have hrow : (∑ f ∈ A, |C e f|) ≤ K * R := by
      calc
        _ = ∑ f ∈ A, |a f| * |v e ⬝ᵥ v f| := by simp only [C, abs_mul]
        _ ≤ ∑ f ∈ A, K * |v e ⬝ᵥ v f| :=
          Finset.sum_le_sum (fun f hf ↦ mul_le_mul_of_nonneg_right (ha f hf) (abs_nonneg _))
        _ ≤ _ := by
          rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left (hcov e he) hK
    have hF : (∫ x, F e x ^ 4 ∂γ) ≤ 848 * (K * R) ^ 4 * D ^ 4 := by
      have h := integral_fourth_weighted_gaussianSquares_le A (C e) v
        (a := 1) zero_le_one hvar hrow
      norm_num only [one_mul, one_pow, Nat.reduceAdd, Nat.reduceMul] at h
      exact h
    have hYLp : MemLp (fun x ↦ Y e x ^ 2) 2 γ := by
      have h : AEStronglyMeasurable (fun x ↦ Y e x ^ 2) γ := by
        have h' := (integrable_eval_standardGaussianProduct (linearPolynomial (v e) ^ 2)).1
        simpa only [map_pow, eval_linearPolynomial, Y] using h'
      exact (memLp_two_iff_integrable_sq h).2 (by simpa only [← pow_mul, Nat.reduceMul] using hYint)
    have hFLp : MemLp (fun x ↦ F e x ^ 2) 2 γ := by
      have h : AEStronglyMeasurable (fun x ↦ F e x ^ 2) γ := by
        have h' := (integrable_eval_standardGaussianProduct (P e ^ 2)).1
        simpa only [map_pow, hP] using h'
      exact (memLp_two_iff_integrable_sq h).2 (by simpa only [← pow_mul, Nat.reduceMul] using hFint)
    have hs := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      (ae_of_all γ (fun x ↦ sq_nonneg (Y e x))) (ae_of_all γ (fun x ↦ sq_nonneg (F e x)))
      (by simpa using hYLp) (by simpa using hFLp)
    simp only [Real.rpow_two, ← pow_mul, Nat.reduceMul, ← Real.sqrt_eq_rpow] at hs
    have hY' : Real.sqrt (∫ x, Y e x ^ 4 ∂γ) ≤ 2 * D := by
      apply (Real.sqrt_le_left (by positivity : 0 ≤ 2 * D)).2
      nlinarith only [hY, sq_nonneg D]
    have hF' : Real.sqrt (∫ x, F e x ^ 4 ∂γ) ≤ 30 * (K * R) ^ 2 * D ^ 2 := by
      apply (Real.sqrt_le_left (by positivity : 0 ≤ 30 * (K * R) ^ 2 * D ^ 2)).2
      nlinarith only [hF, mul_nonneg (pow_nonneg (mul_nonneg hK hR) 4) (pow_nonneg hD 4)]
    have hprod : (∫ x, Y e x ^ 2 * F e x ^ 2 ∂γ) ≤ 60 * (K * R) ^ 2 * D ^ 3 := by
      refine hs.trans ?_
      have h := mul_le_mul hY' hF' (Real.sqrt_nonneg _) (by positivity : 0 ≤ 2 * D)
      exact h.trans_eq (by ring)
    have hz (x : Fin n → ℝ) : Z e x ^ 2 = (144 * a e ^ 2) * (Y e x ^ 2 * F e x ^ 2) := by
      dsimp only [Z]
      ring
    simp_rw [hz]
    rw [integral_const_mul]
    have hcoeff : a e ^ 2 ≤ K ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (ha e he) 2
    have h := mul_le_mul (mul_le_mul_of_nonneg_left hcoeff (by norm_num : 0 ≤ (144 : ℝ))) hprod
      (integral_nonneg (fun _ ↦ by positivity)) (by positivity)
    exact h.trans_eq (by ring)
  refine (variance_mvPolynomial_standardGaussianProduct_le G).trans (hI.trans ?_)
  calc
    _ ≤ lower⁻¹ * ∑ _ ∈ A, 8640 * K ^ 4 * R ^ 2 * D ^ 3 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hZ) (inv_nonneg.mpr hlower.le)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

end BoundedEdgeRegularSubgraphs
