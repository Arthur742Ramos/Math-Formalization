module

public import BoundedEdgeRegularSubgraphs.OverlapInverse
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
# The maximum-norm bound on the inverse of the full covariance
-/

public section

open scoped BigOperators Matrix

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- The inverse row-sum bound for the complete covariance in terms of a
uniform positive lower bound on the Bernoulli variances. -/
theorem degreeCovariance_full_inverse_rows (lower : ℝ) (hlower : 0 < lower) :
    ∃ C : ℝ, 0 < C ∧ ∀ {α : Type*} [Fintype α] [LinearOrder α],
      3 ≤ Fintype.card α → ∀ (q : Edge α → Set.Icc (0 : ℝ) 1),
      (∀ e, lower ≤ (q e : ℝ) * (1 - q e)) →
      IsUnit (degreeCovariance Finset.univ q).det ∧
      ∀ i, (∑ j, |(degreeCovariance Finset.univ q)⁻¹ i j|) ≤ C / Fintype.card α := by
  let a := lower / 3
  have ha : 0 < a := by dsimp [a]; positivity
  refine ⟨a⁻¹ + (1 / 4 : ℝ) / a ^ 2 + (1 / 4 : ℝ) ^ 2 / a ^ 3, by positivity, ?_⟩
  intro β _ _ hn q hq
  classical
  let S : Finset β := ∅
  have hcard : ((Finset.univ : Finset β) \ S).card = Fintype.card β := by simp [S]
  have h := degreeCovariance_outside_overlap_inverse_bounds S (by rwa [hcard])
    q lower hlower hq
  let k : ℝ := Fintype.card β
  have hk : 0 < k := by dsimp only [k]; exact_mod_cast (show 0 < Fintype.card β by omega)
  have hA : edgesOutsideOverlap S = Finset.univ := by
    ext e
    simp [edgesOutsideOverlap, S]
  dsimp only at h
  rw [hcard, hA] at h
  have hc : lower * k ^ 2 / (3 * k) = a * k := by
    dsimp [a]
    field_simp
  change IsUnit (degreeCovariance Finset.univ q).det ∧ _
  refine ⟨h.1, ?_⟩
  intro i
  refine (h.2.2.2 i).trans_eq ?_
  change (lower * k ^ 2 / (3 * k))⁻¹ +
      k * ((1 / 4 : ℝ) / (lower * k ^ 2 / (3 * k)) ^ 2 +
        k * (1 / 4 : ℝ) ^ 2 / (lower * k ^ 2 / (3 * k)) ^ 3) =
    (a⁻¹ + (1 / 4 : ℝ) / a ^ 2 + (1 / 4 : ℝ) ^ 2 / a ^ 3) / k
  rw [hc]
  field_simp
  ring

omit [LinearOrder α] in
/-- A row-sum bound controls the maximum norm of matrix multiplication. -/
theorem matrix_mulVec_norm_le_of_row_sum (A : Matrix α α ℝ) {L : ℝ}
    (hL : 0 ≤ L) (hA : ∀ i, (∑ j, |A i j|) ≤ L) (x : α → ℝ) :
    ‖A *ᵥ x‖ ≤ L * ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hL (norm_nonneg x))).mpr
  intro i
  rw [Real.norm_eq_abs, Matrix.mulVec, dotProduct]
  calc
    _ ≤ ∑ j, |A i j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |A i j| * |x j| := Finset.sum_congr rfl (fun j _ ↦ abs_mul _ _)
    _ ≤ ∑ j, |A i j| * ‖x‖ := by
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      rw [← Real.norm_eq_abs]
      exact norm_le_pi_norm x j
    _ = (∑ j, |A i j|) * ‖x‖ := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hA i) (norm_nonneg x)

end BoundedEdgeRegularSubgraphs
