module

public import BoundedEdgeRegularSubgraphs.GaussianCubicMoment
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Mul
import Mathlib.Tactic

/-!
# Fourth moments of weighted sums of Gaussian squares
-/

public section

open MeasureTheory Matrix MvPolynomial
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

private theorem pow_four_weighted_sum_le {ι : Type*} (A : Finset ι) (w z : ι → ℝ)
    (hw : ∀ e ∈ A, 0 ≤ w e) (hz : ∀ e ∈ A, 0 ≤ z e) :
    (∑ e ∈ A, w e * z e) ^ 4 ≤ (∑ e ∈ A, w e) ^ 3 * ∑ e ∈ A, w e * z e ^ 4 := by
  let s := ∑ e ∈ A, w e
  let S := ∑ e ∈ A, w e * z e
  let T := ∑ e ∈ A, w e * z e ^ 4
  have hs : 0 ≤ s := Finset.sum_nonneg hw
  change S ^ 4 ≤ s ^ 3 * T
  rcases hs.eq_or_lt with hs₀ | hs₀
  · have hz₀ : ∀ e ∈ A, w e = 0 := (Finset.sum_eq_zero_iff_of_nonneg hw).1 hs₀.symm
    have hS : S = 0 := Finset.sum_eq_zero (fun e he ↦ by rw [hz₀ e he, zero_mul])
    rw [← hs₀, hS]
    norm_num
  · have h := (convexOn_pow (𝕜 := ℝ) 4).map_centerMass_le hw hs₀
      (fun e he ↦ show z e ∈ Set.Ici 0 from hz e he)
    change (s⁻¹ * S) ^ 4 ≤ s⁻¹ * T at h
    have hh := mul_le_mul_of_nonneg_left h (pow_nonneg hs₀.le 4)
    convert hh using 1 <;> field_simp [hs₀.ne']

private theorem add_pow_four_le (x y : ℝ) :
    (x + y) ^ 4 ≤ 8 * (x ^ 4 + y ^ 4) := by
  have h := show (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) by nlinarith only [sq_nonneg (x - y)]
  have hs := pow_le_pow_left₀ (sq_nonneg (x + y)) h 2
  nlinarith only [hs, sq_nonneg (x ^ 2 - y ^ 2)]

/-- A row-sum bound on the coefficients controls the fourth moment of
the Gaussian squares in a projected gradient from Lemma A.2. -/
theorem integral_fourth_weighted_gaussianSquares_le {n : ℕ} {ι : Type*}
    (A : Finset ι) (b : ι → ℝ) (v : ι → Fin n → ℝ) {a D R : ℝ}
    (ha : 0 ≤ a) (hD : ∀ e ∈ A, (∑ i, v e i ^ 2) ≤ D)
    (hR : (∑ e ∈ A, |b e|) ≤ R) :
    (∫ x, (∑ e ∈ A, b e * ((v e ⬝ᵥ x) ^ 2 + a * (∑ i, v e i ^ 2))) ^ 4
      ∂standardGaussianProduct n) ≤ 8 * (105 + a ^ 4) * R ^ 4 * D ^ 4 := by
  let γ := standardGaussianProduct n
  let q (e : ι) := ∑ i, v e i ^ 2
  let y (e : ι) (x : Fin n → ℝ) := v e ⬝ᵥ x
  let z (e : ι) (x : Fin n → ℝ) := y e x ^ 2 + a * q e
  let w (e : ι) := |b e|
  let s := ∑ e ∈ A, w e
  let P (e : ι) : MvPolynomial (Fin n) ℝ := linearPolynomial (v e) ^ 2 + C (a * q e)
  let L (x : Fin n → ℝ) := (∑ e ∈ A, b e * z e x) ^ 4
  have hq₀ (e : ι) : 0 ≤ q e := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hz₀ (e : ι) (x : Fin n → ℝ) : 0 ≤ z e x :=
    add_nonneg (sq_nonneg _) (mul_nonneg ha (hq₀ e))
  have hs : 0 ≤ s := Finset.sum_nonneg (fun e _ ↦ abs_nonneg _)
  have hR₀ : 0 ≤ R := hs.trans hR
  have hP (e : ι) (x : Fin n → ℝ) : eval x (P e) = z e x := by
    simp only [P, z, y, map_add, map_pow, eval_C, eval_linearPolynomial]
  have hLi : Integrable L γ := by
    have he : (fun x : Fin n → ℝ ↦ eval x ((∑ e ∈ A, C (b e) * P e) ^ 4)) = L := by
      funext x
      simp only [L, map_pow, map_sum, map_mul, eval_C, hP]
    rw [← he]
    exact integrable_eval_standardGaussianProduct _
  have hiz (e : ι) : Integrable (fun x ↦ z e x ^ 4) γ := by
    have he (x : Fin n → ℝ) : eval x (P e ^ 4) = z e x ^ 4 := by rw [map_pow, hP]
    rw [← funext he]
    exact integrable_eval_standardGaussianProduct _
  have hpoint (x : Fin n → ℝ) : L x ≤ s ^ 3 * ∑ e ∈ A, w e * z e x ^ 4 := by
    have h₁ : |∑ e ∈ A, b e * z e x| ≤ ∑ e ∈ A, w e * z e x := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
      exact Finset.sum_congr rfl (fun e _ ↦ by rw [abs_mul, abs_of_nonneg (hz₀ e x)])
    have h₁' := pow_le_pow_left₀ (abs_nonneg _) h₁ 4
    have he (t : ℝ) : |t| ^ 4 = t ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, sq_abs, ← pow_mul]
    rw [he] at h₁'
    exact h₁'.trans (pow_four_weighted_sum_le A w (fun e ↦ z e x)
      (fun e _ ↦ abs_nonneg _) (fun e _ ↦ hz₀ e x))
  have hiw (e : ι) (_ : e ∈ A) : Integrable (fun x ↦ w e * z e x ^ 4) γ :=
    (hiz e).const_mul _
  have hL := integral_mono hLi ((integrable_finsetSum A hiw).const_mul (s ^ 3)) hpoint
  rw [integral_const_mul, integral_finsetSum _ hiw] at hL
  simp_rw [integral_const_mul] at hL
  have hm (e : ι) (he : e ∈ A) : (∫ x, z e x ^ 4 ∂γ) ≤ 8 * (105 + a ^ 4) * D ^ 4 := by
    have hi : Integrable (fun x ↦ y e x ^ 8) γ := by
      have heq (x : Fin n → ℝ) : eval x (linearPolynomial (v e) ^ 8) = y e x ^ 8 := by
        rw [map_pow, eval_linearPolynomial]
      rw [← funext heq]
      exact integrable_eval_standardGaussianProduct _
    have hn (x : Fin n → ℝ) : z e x ^ 4 ≤ 8 * (y e x ^ 8 + (a * q e) ^ 4) := by
      have h := add_pow_four_le (y e x ^ 2) (a * q e)
      change (y e x ^ 2 + a * q e) ^ 4 ≤ _
      rw [← pow_mul] at h
      exact h
    have h := integral_mono (hiz e) ((hi.add (integrable_const _)).const_mul 8) hn
    rw [integral_const_mul] at h
    simp only [Pi.add_apply] at h
    rw [integral_add hi (integrable_const ((a * q e) ^ 4)), integral_const,
      probReal_univ, one_smul] at h
    have h₈ := integral_even_pow_dotProduct_standardGaussianProduct (v e) 4
    norm_num [Finset.prod_range_succ] at h₈
    have h₈' : (∫ x, y e x ^ 8 ∂γ) = 105 * q e ^ 4 := by
      simpa only [mul_comm (105 : ℝ)] using h₈
    rw [h₈', mul_pow] at h
    refine h.trans ?_
    have hpow := pow_le_pow_left₀ (hq₀ e) (hD e he) 4
    nlinarith only [mul_le_mul_of_nonneg_left hpow (show 0 ≤ 8 * (105 + a ^ 4) by positivity)]
  refine hL.trans ?_
  let C₀ := 8 * (105 + a ^ 4) * D ^ 4
  have hC : 0 ≤ C₀ := by dsimp only [C₀]; positivity
  calc
    _ ≤ s ^ 3 * ∑ e ∈ A, w e * C₀ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun e he ↦
        mul_le_mul_of_nonneg_left (hm e he) (abs_nonneg _))) (pow_nonneg hs _)
    _ = C₀ * s ^ 4 := by rw [← Finset.sum_mul]; change s ^ 3 * (s * C₀) = _; ring
    _ ≤ C₀ * R ^ 4 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs hR 4) hC
    _ = _ := by dsimp only [C₀]; ring

end BoundedEdgeRegularSubgraphs
