module

public import BoundedEdgeRegularSubgraphs.OverlapCovariance
public import BoundedEdgeRegularSubgraphs.CovarianceInverse
import Mathlib.Tactic

/-!
# Entrywise estimates for the inverse degree covariance
-/

public section

open scoped BigOperators Matrix

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]

omit [Fintype α] in
private theorem covariance_symm (A : Finset (Edge α)) (p : Edge α → Set.Icc (0 : ℝ) 1)
    (i j : α) : degreeCovariance A p i j = degreeCovariance A p j i := by
  unfold degreeCovariance
  exact Finset.sum_congr rfl (fun e _ ↦ by ring)

omit [Fintype α] in
private theorem incidence_nonzero (e : Edge α) (i : α) (h : edgeIncidence e i ≠ 0) :
    i = e.val.1 ∨ i = e.val.2 := by
  by_contra! hn
  exact h (by simp [edgeIncidence, hn.1, hn.2])

omit [Fintype α] in
private theorem covariance_offDiag_le_of_lt (A : Finset (Edge α)) (p : Edge α → Set.Icc (0 : ℝ) 1)
    {i j : α} (hij : i < j) : |degreeCovariance A p i j| ≤ 1 / 4 := by
  classical
  let e₀ : Edge α := ⟨(i, j), hij⟩
  let term (e : Edge α) := (p e : ℝ) * (1 - p e) *
    (edgeIncidence e i : ℝ) * (edgeIncidence e j : ℝ)
  have hterm (e : Edge α) (he : e ≠ e₀) : term e = 0 := by
    by_cases hi : edgeIncidence e i = 0
    · simp [term, hi]
    by_cases hj : edgeIncidence e j = 0
    · simp [term, hj]
    exfalso
    apply he
    rcases incidence_nonzero e i hi with h₁ | h₁ <;>
      rcases incidence_nonzero e j hj with h₂ | h₂
    · exact (ne_of_lt hij (h₁.trans h₂.symm)).elim
    · exact Subtype.ext (Prod.ext h₁.symm h₂.symm)
    · have hji : j < i := by rw [h₁, h₂]; exact e.property
      exact (lt_asymm hij hji).elim
    · exact (ne_of_lt hij (h₁.trans h₂.symm)).elim
  change |∑ e ∈ A, term e| ≤ 1 / 4
  by_cases h : e₀ ∈ A
  · rw [Finset.sum_eq_single_of_mem e₀ h (fun e _ he ↦ hterm e he)]
    have hv : term e₀ = (p e₀ : ℝ) * (1 - p e₀) := by
      simp [term, edgeIncidence, e₀, ne_of_lt hij, ne_of_gt hij]
    rw [hv, abs_of_nonneg (mul_nonneg (p e₀).property.1 (sub_nonneg.mpr (p e₀).property.2))]
    nlinarith only [sq_nonneg ((p e₀ : ℝ) - 1 / 2)]
  · rw [Finset.sum_eq_zero (fun e he ↦ hterm e (by rintro rfl; exact h he)), abs_zero]
    norm_num

omit [Fintype α] in
/-- Each off-diagonal covariance entry is bounded by one Bernoulli variance. -/
theorem degreeCovariance_offDiag_le (A : Finset (Edge α)) (p : Edge α → Set.Icc (0 : ℝ) 1)
    {i j : α} (hij : i ≠ j) : |degreeCovariance A p i j| ≤ 1 / 4 := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact covariance_offDiag_le_of_lt A p h
  · rw [covariance_symm A p i j]
    exact covariance_offDiag_le_of_lt A p h

/-- Explicit diagonal, off-diagonal and absolute row-sum bounds after deleting an overlap. -/
theorem degreeCovariance_outside_overlap_inverse_bounds (S : Finset α)
    (hm : 3 ≤ ((Finset.univ : Finset α) \ S).card)
    (p : Edge α → Set.Icc (0 : ℝ) 1) (lower : ℝ) (hlower : 0 < lower)
    (hp : ∀ e, lower ≤ (p e : ℝ) * (1 - p e)) :
    let c : ℝ := lower * (((Finset.univ : Finset α) \ S).card : ℝ) ^ 2 / (3 * Fintype.card α)
    let Q := degreeCovariance (edgesOutsideOverlap S) p
    let r := (1 / 4 : ℝ) / c ^ 2 + (Fintype.card α : ℝ) * (1 / 4 : ℝ) ^ 2 / c ^ 3
    IsUnit Q.det ∧ (∀ i, |Q⁻¹ i i| ≤ c⁻¹) ∧
      (∀ i j, i ≠ j → |Q⁻¹ i j| ≤ r) ∧
      (∀ i, (∑ j, |Q⁻¹ i j|) ≤ c⁻¹ + (Fintype.card α : ℝ) * r) := by
  classical
  dsimp only
  let m := ((Finset.univ : Finset α) \ S).card
  let c : ℝ := lower * (m : ℝ) ^ 2 / (3 * Fintype.card α)
  let Q := degreeCovariance (edgesOutsideOverlap S) p
  let r := (1 / 4 : ℝ) / c ^ 2 + (Fintype.card α : ℝ) * (1 / 4 : ℝ) ^ 2 / c ^ 3
  change IsUnit Q.det ∧ (∀ i, |Q⁻¹ i i| ≤ c⁻¹) ∧
      (∀ i j, i ≠ j → |Q⁻¹ i j| ≤ r) ∧
      (∀ i, (∑ j, |Q⁻¹ i j|) ≤ c⁻¹ + (Fintype.card α : ℝ) * r)
  have hmpos : 0 < m := by dsimp [m]; omega
  have hnpos : 0 < Fintype.card α := hmpos.trans_le (Finset.card_le_univ _)
  have hmpos' : 0 < (m : ℝ) := by exact_mod_cast hmpos
  have hnpos' : 0 < (Fintype.card α : ℝ) := by exact_mod_cast hnpos
  have hc : 0 < c := by dsimp [c]; positivity
  have hquad (v : α → ℝ) : c * (∑ i, v i ^ 2) ≤ v ⬝ᵥ (Q *ᵥ v) := by
    have h := (degreeCovariance_outside_overlap_bounds S hm p lower hlower.le hp v).1
    have hleft : c = lower * ((m : ℝ) ^ 2 / (3 * Fintype.card α)) := by
      dsimp [c]
      rw [mul_div_assoc]
    have hright : v ⬝ᵥ (Q *ᵥ v) = ∑ i, ∑ j, v i * Q i j * v j := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    rw [hleft, hright]
    exact h
  have hdet := (inverse_mulVec_sq_le_of_quadratic Q hc hquad).1
  obtain ⟨hdiag, hoff⟩ := inverse_entry_bounds Q hc (by norm_num : 0 ≤ (1 / 4 : ℝ)) hquad
    (fun _ _ hij ↦ degreeCovariance_offDiag_le _ p hij)
  refine ⟨hdet, hdiag, hoff, ?_⟩
  intro i
  have hr : 0 ≤ r := by dsimp [r]; positivity
  rw [← Finset.sum_erase_add Finset.univ (fun j ↦ |Q⁻¹ i j|) (Finset.mem_univ i)]
  calc
    _ ≤ (∑ _ ∈ Finset.univ.erase i, r) + c⁻¹ := by
      apply add_le_add _ (hdiag i)
      exact Finset.sum_le_sum (fun j hj ↦ hoff i j (Ne.symm (Finset.ne_of_mem_erase hj)))
    _ ≤ _ := by
      rw [Finset.sum_const, nsmul_eq_mul, add_comm]
      have hk : ((Finset.univ.erase i).card : ℝ) ≤ Fintype.card α := by
        exact_mod_cast Finset.card_le_univ (Finset.univ.erase i)
      exact add_le_add_right (mul_le_mul_of_nonneg_right hk hr) _

end BoundedEdgeRegularSubgraphs
