module

public import BoundedEdgeRegularSubgraphs.IntersectionSampling
import Mathlib.Tactic

/-!
# The probability mass of a fixed overlap size
-/

@[expose] public section

open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

noncomputable def overlapMass (N k j : ℕ) : ℝ :=
  ((N - k).choose (k - j) : ℝ) * (k.choose j : ℝ) / (N.choose k : ℝ)

variable {α : Type*} [DecidableEq α]

theorem card_overlap_samples (s S : Finset α) (hS : S ⊆ s) {k j : ℕ}
    (hSk : S.card = k) (hj : j ≤ k) :
    (((s.powersetCard k).filter fun T ↦ (S ∩ T).card = j).card : ℝ) =
      ((s.card - k).choose (k - j) : ℝ) * (k.choose j : ℝ) := by
  simpa only [Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard, Finset.card_sdiff_of_subset hS,
    hSk, mul_one] using sum_sample_intersection_of_card s S hS hj (fun _ ↦ (1 : ℝ))

theorem overlapMass_nonneg (N k j : ℕ) : 0 ≤ overlapMass N k j := by
  unfold overlapMass
  positivity

theorem sum_overlapMass_eq_one (s S : Finset α) (hS : S ⊆ s) {k : ℕ} (hSk : S.card = k) :
    ∑ j ∈ Finset.range (k + 1), overlapMass s.card k j = 1 := by
  classical
  have hk : k ≤ s.card := hSk ▸ Finset.card_le_card hS
  have hChoose : 0 < (s.card.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hk
  unfold overlapMass
  rw [← Finset.sum_div, div_eq_iff hChoose.ne', one_mul]
  calc
    _ = ∑ j ∈ Finset.range (k + 1),
        (((s.powersetCard k).filter fun T ↦ (S ∩ T).card = j).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (card_overlap_samples s S hS hSk (by have := Finset.mem_range.mp hj; omega)).symm
    _ = ∑ T ∈ s.powersetCard k, ∑ j ∈ Finset.range (k + 1),
        if (S ∩ T).card = j then (1 : ℝ) else 0 := by
      rw [Finset.sum_comm]
      simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = _ := by
      rw [← Finset.card_powersetCard]
      calc
        _ = ∑ _T ∈ s.powersetCard k, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro T _
          have hi : (S ∩ T).card ∈ Finset.range (k + 1) := by
            have h : (S ∩ T).card ≤ k := (Finset.card_le_card Finset.inter_subset_left).trans_eq hSk
            exact Finset.mem_range.mpr (by omega)
          rw [Finset.sum_eq_single_of_mem _ hi (fun j _ hj ↦ ite_eq_right (Ne.symm hj)), ite_eq_left rfl]
        _ = _ := by simp

theorem overlapMass_le_pow (s S : Finset α) (hS : S ⊆ s) {k j : ℕ} (hSk : S.card = k)
    (hj : 0 < j) (hjk : j ≤ k) :
    overlapMass s.card k j ≤ (Real.exp 1 * ((k : ℝ) ^ 2 / s.card) / j) ^ j := by
  have hk : k ≤ s.card := hSk ▸ Finset.card_le_card hS
  have hChoose : 0 < (s.card.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hk
  have h := card_sample_intersection_eq_le s S hS hSk hj hjk
  rw [card_overlap_samples s S hS hSk hjk] at h
  apply (div_le_iff₀ hChoose).2
  exact h.trans (by
    rw [mul_comm _ (s.card.choose k : ℝ)]
    exact mul_le_mul_of_nonneg_left (min_le_right _ _) hChoose.le)

/-- A pointwise ratio bound controls the contribution of one overlap size. -/
theorem sum_overlapBand_le_of_pointwise (s : Finset α) {k j : ℕ} (F : Finset (Finset α))
    (hF : F ⊆ s.powersetCard k) (hj : j ≤ k) (R : Finset α → Finset α → ℝ)
    {B : ℝ} (hB : 0 ≤ B)
    (hRatio : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).card = j → R S T ≤ B) :
    (∑ S ∈ F, ∑ T ∈ F, if (S ∩ T).card = j then R S T else 0) ≤
      (F.card : ℝ) * (((s.card - k).choose (k - j) : ℝ) * (k.choose j : ℝ)) * B := by
  classical
  calc
    _ ≤ ∑ S ∈ F, ∑ T ∈ F, if (S ∩ T).card = j then B else 0 := by
      apply Finset.sum_le_sum
      intro S hS
      apply Finset.sum_le_sum
      intro T hT
      split_ifs with h
      · exact hRatio S hS T hT h
      · rfl
    _ ≤ ∑ S ∈ F, ∑ T ∈ s.powersetCard k, if (S ∩ T).card = j then B else 0 := by
      apply Finset.sum_le_sum
      intro S _
      exact Finset.sum_le_sum_of_subset_of_nonneg hF (fun _ _ _ ↦ by split_ifs <;> positivity)
    _ = _ := by
      simp_rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have hEq (S : Finset α) (hS : S ∈ F) :=
        card_overlap_samples s S (Finset.mem_powersetCard.mp (hF hS)).1
          (Finset.mem_powersetCard.mp (hF hS)).2 hj
      calc
        _ = ∑ _S ∈ F, (((s.card - k).choose (k - j) : ℝ) * (k.choose j : ℝ)) * B := by
          apply Finset.sum_congr rfl
          intro S hS
          rw [hEq S hS]
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

end BoundedEdgeRegularSubgraphs
