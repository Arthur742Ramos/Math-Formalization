module

public import BoundedEdgeRegularSubgraphs.SampleDriftEnergy
import Mathlib.Tactic

/-!
# Uniform approximation of retained row means
-/

public section

open Set
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

/-- The number of samples with a retained row mean outside the given
tolerance is bounded by the union of the conditional sampling tails. -/
theorem card_samples_rowMean_bad_le {α : Type*} [DecidableEq α] (s : Finset α)
    (q : α → α → ℝ) {m : ℕ} (hm : 2 ≤ m) (hms : m ≤ s.card)
    (hq : ∀ i ∈ s, ∀ j ∈ s.erase i, q i j ∈ Icc (0 : ℝ) 1) {v : ℝ} (hv : 0 ≤ v) :
    (((s.powersetCard m).filter (fun S ↦ ∃ i ∈ S,
      v < |sampleRowMean S q i - sampleRowMean s q i|)).card : ℝ) ≤
      (s.card.choose m : ℝ) * (2 * (m : ℝ) * Real.exp (-2 * ((m - 1 : ℕ) : ℝ) * v ^ 2)) := by
  classical
  let F := s.powersetCard m
  let r := m - 1
  let U (i : α) := (s.erase i).powersetCard r
  let bad (i : α) (T : Finset α) :=
    (r : ℝ) * v ≤ |(∑ j ∈ T, q i j) - (r : ℝ) * sampleRowMean s q i|
  let W (S : Finset α) := ∃ i ∈ S, v < |sampleRowMean S q i - sampleRowMean s q i|
  let f (i : α) (T : Finset α) := if bad i T then (1 : ℝ) else 0
  have hr : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hw (S : Finset α) (hS : S ∈ F) : (if W S then (1 : ℝ) else 0) ≤ ∑ i ∈ S, f i (S.erase i) := by
    by_cases h : W S
    · obtain ⟨i, hi, hv'⟩ := h
      rw [ite_eq_left (show W S from ⟨i, hi, hv'⟩)]
      have hc : S.card = m := (Finset.mem_powersetCard.mp hS).2
      have hbad : bad i (S.erase i) := by
        change v < |(∑ j ∈ S.erase i, q i j) / ((S.card - 1 : ℕ) : ℝ) - sampleRowMean s q i| at hv'
        rw [hc] at hv'
        change v < |(∑ j ∈ S.erase i, q i j) / (r : ℝ) - sampleRowMean s q i| at hv'
        have he : (∑ j ∈ S.erase i, q i j) / (r : ℝ) - sampleRowMean s q i =
            ((∑ j ∈ S.erase i, q i j) - (r : ℝ) * sampleRowMean s q i) / (r : ℝ) := by
          field_simp [hr.ne'] <;> ring
        rw [he, abs_div, abs_of_pos hr, lt_div_iff₀ hr] at hv'
        have hv'' := hv'.le
        rw [mul_comm v] at hv''
        exact hv''
      rw [← show f i (S.erase i) = 1 from ite_eq_left hbad]
      exact Finset.single_le_sum (f := fun j ↦ f j (S.erase j))
        (fun j _ ↦ by unfold f; split_ifs <;> norm_num) hi
    · rw [ite_eq_right h]
      exact Finset.sum_nonneg (fun i _ ↦ by unfold f; split_ifs <;> norm_num)
  have hc : ((F.filter W).card : ℝ) = ∑ S ∈ F, if W S then (1 : ℝ) else 0 := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  change ((F.filter W).card : ℝ) ≤ _
  rw [hc]
  refine (Finset.sum_le_sum hw).trans ?_
  rw [sum_samples_distinguished_vertex s (show 0 < m by omega) f]
  have hcount (i : α) (hi : i ∈ s) : (∑ T ∈ U i, f i T) ≤
      2 * ((s.card - 1).choose r : ℝ) * Real.exp (-2 * (r : ℝ) * v ^ 2) := by
    have hc' : (s.erase i).card = s.card - 1 := Finset.card_erase_of_mem hi
    have hpos : 0 < (s.erase i).card := by rw [hc']; omega
    have h := card_sample_abs_deviation_le (s.erase i) (q i) hpos (hq i hi) r hv
    dsimp only at h
    rw [hc'] at h
    simp only [f, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    exact h
  refine (Finset.sum_le_sum hcount).trans_eq ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have h := card_mul_choose_pred s (show 0 < m by omega)
  have hh : (m : ℝ) * (s.card.choose m : ℝ) = (s.card : ℝ) * ((s.card - 1).choose r : ℝ) := by
    exact_mod_cast h
  linear_combination -(2 * Real.exp (-2 * (r : ℝ) * v ^ 2)) * hh

/-- Positive success probability gives a deterministic sample whose
retained rows approximate their original normalized degrees. -/
theorem exists_sample_rowMean_close {α : Type*} [DecidableEq α] (s : Finset α)
    (q : α → α → ℝ) {m : ℕ} (hm : 2 ≤ m) (hms : m ≤ s.card)
    (hq : ∀ i ∈ s, ∀ j ∈ s.erase i, q i j ∈ Icc (0 : ℝ) 1) {v : ℝ} (hv : 0 ≤ v)
    (hsmall : 2 * (m : ℝ) * Real.exp (-2 * ((m - 1 : ℕ) : ℝ) * v ^ 2) < 1) :
    ∃ T ⊆ s, T.card = m ∧ ∀ i ∈ T, |sampleRowMean T q i - sampleRowMean s q i| ≤ v := by
  classical
  let F := s.powersetCard m
  let W (S : Finset α) := ∃ i ∈ S, v < |sampleRowMean S q i - sampleRowMean s q i|
  have h := card_samples_rowMean_bad_le s q hm hms hq hv
  have hc : 0 < (s.card.choose m : ℝ) := by exact_mod_cast Nat.choose_pos hms
  have hlt : (↑(F.filter W).card : ℝ) < F.card := by
    have hh := mul_lt_mul_of_pos_left hsmall hc
    rw [mul_one] at hh
    have hh' : (F.card : ℝ) = (s.card.choose m : ℝ) := by simp [F]
    exact (h.trans_lt hh).trans_eq hh'.symm
  have hNS : ¬ F ⊆ F.filter W := by
    intro hs
    have h' : (F.card : ℝ) ≤ (F.filter W).card := by exact_mod_cast Finset.card_le_card hs
    exact (not_lt_of_ge h') hlt
  obtain ⟨T, hT, hTN⟩ := Finset.not_subset.mp hNS
  obtain ⟨hTS, hcard⟩ := Finset.mem_powersetCard.mp hT
  exact ⟨T, hTS, hcard, fun i hi ↦ le_of_not_gt (fun hh ↦ hTN (Finset.mem_filter.mpr ⟨hT, i, hi, hh⟩))⟩

end BoundedEdgeRegularSubgraphs
