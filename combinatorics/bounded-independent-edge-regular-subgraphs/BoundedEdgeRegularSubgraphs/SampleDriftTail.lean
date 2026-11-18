module

public import BoundedEdgeRegularSubgraphs.SampleDriftEnergy
import Mathlib.Tactic

/-!
# Uniform candidate selection by the two drift estimates
-/

public section

open Set
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [DecidableEq α]

/-- A bad maximum drift is witnessed by a distinguished vertex. -/
theorem card_samples_large_drift_le (s : Finset α) (q : α → α → ℝ)
    {k : ℕ} (hk : 2 ≤ k) (hks : k ≤ s.card) (p d : ℝ) {a v : ℝ} (hv : 0 ≤ v)
    (hq : ∀ i ∈ s, ∀ j ∈ s.erase i, q i j ∈ Icc (0 : ℝ) 1)
    (hd : |p * ((k - 1 : ℕ) : ℝ) - d| ≤ 1)
    (ha : ∀ i ∈ s, |sampleRowMean s q i - p| ≤ a) :
    let m := ((k - 1 : ℕ) : ℝ)
    (((s.powersetCard k).filter (fun S ↦ ∃ i ∈ S,
      m * a + 1 + m * v < |sampleRowDrift S q d i|)).card : ℝ) ≤
        (s.card.choose k : ℝ) * (2 * k * Real.exp (-2 * m * v ^ 2)) := by
  classical
  let X := s.powersetCard k
  let m := k - 1
  let b := (s.card - 1).choose m
  let t := (m : ℝ) * a + 1 + (m : ℝ) * v
  let F (i : α) (T : Finset α) : ℝ := if t < |(∑ j ∈ T, q i j) - d| then 1 else 0
  let W (S : Finset α) := ∃ i ∈ S, t < |sampleRowDrift S q d i|
  have hx : ((X.filter W).card : ℝ) = ∑ S ∈ X, if W S then (1 : ℝ) else 0 := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hpoint (S : Finset α) (_ : S ∈ X) : (if W S then (1 : ℝ) else 0) ≤
      ∑ i ∈ S, F i (S.erase i) := by
    by_cases h : W S
    · obtain ⟨i, hi, hi'⟩ := h
      rw [if_pos (show W S from ⟨i, hi, hi'⟩)]
      have hw : F i (S.erase i) = 1 := if_pos hi'
      rw [← hw]
      exact Finset.single_le_sum (f := fun j ↦ F j (S.erase j))
        (fun j _ ↦ by unfold F; split_ifs <;> norm_num) hi
    · rw [if_neg h]
      exact Finset.sum_nonneg (fun j _ ↦ by unfold F; split_ifs <;> norm_num)
  change ((X.filter W).card : ℝ) ≤ _
  rw [hx]
  refine (Finset.sum_le_sum hpoint).trans ?_
  rw [sum_samples_distinguished_vertex s (show 0 < k by omega) F]
  have hvertex (i : α) (his : i ∈ s) :
      (∑ T ∈ (s.erase i).powersetCard m, F i T) ≤
        2 * (b : ℝ) * Real.exp (-2 * (m : ℝ) * v ^ 2) := by
    let Y := (s.erase i).powersetCard m
    let D (T : Finset α) := (∑ j ∈ T, q i j) - (m : ℝ) * sampleRowMean s q i
    have hc : (s.erase i).card = s.card - 1 := Finset.card_erase_of_mem his
    have hi : 0 < (s.erase i).card := by rw [hc]; omega
    have hh := card_sample_abs_deviation_le (s.erase i) (q i) hi (hq i his) m hv
    dsimp only at hh
    rw [hc] at hh
    have hμ : |(m : ℝ) * sampleRowMean s q i - d| ≤ (m : ℝ) * a + 1 := by
      have he : (m : ℝ) * sampleRowMean s q i - d =
          (m : ℝ) * (sampleRowMean s q i - p) + ((m : ℝ) * p - d) := by ring
      rw [he]
      apply (abs_add_le _ _).trans
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg m)]
      exact add_le_add (mul_le_mul_of_nonneg_left (ha i his) (Nat.cast_nonneg m))
        (by simpa only [mul_comm p] using hd)
    have hIncl : Y.filter (fun T ↦ t < |(∑ j ∈ T, q i j) - d|) ⊆
        Y.filter (fun T ↦ (m : ℝ) * v ≤ |D T|) := by
      intro T hT
      obtain ⟨hY, ht⟩ := Finset.mem_filter.mp hT
      apply Finset.mem_filter.mpr
      refine ⟨hY, ?_⟩
      have he : (∑ j ∈ T, q i j) - d = D T + ((m : ℝ) * sampleRowMean s q i - d) := by
        dsimp only [D]
        ring
      rw [he] at ht
      dsimp only [t] at ht
      linarith only [ht, abs_add_le (D T) ((m : ℝ) * sampleRowMean s q i - d), hμ]
    change (∑ T ∈ Y, F i T) ≤ _
    simp only [F, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    exact (Nat.cast_le.mpr (Finset.card_le_card hIncl)).trans hh
  refine (Finset.sum_le_sum hvertex).trans_eq ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have h := card_mul_choose_pred s (show 0 < k by omega)
  have h' : (k : ℝ) * (s.card.choose k : ℝ) = (s.card : ℝ) * (b : ℝ) := by exact_mod_cast h
  linear_combination -(2 * Real.exp (-2 * (m : ℝ) * v ^ 2)) * h'

/-- At least half of the samples satisfy both the maximum-drift
and squared-drift estimates once the scalar tail is small enough. -/
theorem card_candidate_drift_bounds (s : Finset α) (q : α → α → ℝ)
    {k : ℕ} (hk : 2 ≤ k) (hks : k ≤ s.card) (p d η : ℝ) {a v : ℝ} (hv : 0 ≤ v)
    (hq : ∀ i ∈ s, ∀ j ∈ s.erase i, q i j ∈ Icc (0 : ℝ) 1)
    (hd : |p * ((k - 1 : ℕ) : ℝ) - d| ≤ 1)
    (ha : ∀ i ∈ s, |sampleRowMean s q i - p| ≤ a)
    (hη : (∑ i ∈ s, (sampleRowMean s q i - p) ^ 2) ≤ (s.card : ℝ) * η ^ 2)
    (hsmall : 2 * (k : ℝ) * Real.exp (-2 * ((k - 1 : ℕ) : ℝ) * v ^ 2) ≤ 1 / 4) :
    let m := ((k - 1 : ℕ) : ℝ)
    let good := (s.powersetCard k).filter (fun S ↦
      (∀ i ∈ S, |sampleRowDrift S q d i| ≤ m * a + 1 + m * v) ∧
      (∑ i ∈ S, sampleRowDrift S q d i ^ 2) ≤
        8 * (k : ℝ) ^ 2 + 8 * η ^ 2 * (k : ℝ) ^ 3)
    (s.card.choose k : ℝ) / 2 ≤ (good.card : ℝ) := by
  classical
  let X := s.powersetCard k
  let m := ((k - 1 : ℕ) : ℝ)
  let t := m * a + 1 + m * v
  let E (S : Finset α) := ∑ i ∈ S, sampleRowDrift S q d i ^ 2
  let R := 2 * (k : ℝ) ^ 2 + 2 * η ^ 2 * (k : ℝ) ^ 3
  let G := X.filter (fun S ↦ (∀ i ∈ S, |sampleRowDrift S q d i| ≤ t) ∧ E S ≤ 4 * R)
  let B₁ := X.filter (fun S ↦ ∃ i ∈ S, t < |sampleRowDrift S q d i|)
  let B₂ := X.filter (fun S ↦ 4 * R < E S)
  have hcount : (X.card : ℝ) = s.card.choose k := by simp only [X, Finset.card_powersetCard]
  have hB₁ : (B₁.card : ℝ) ≤ (X.card : ℝ) / 4 := by
    have h := card_samples_large_drift_le s q hk hks p d hv hq hd ha
    refine h.trans ?_
    rw [hcount]
    exact (mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg (s.card.choose k) : (0 : ℝ) ≤ _)).trans_eq
      (by ring)
  have hR : 0 < R := by
    have hk₀ : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    dsimp only [R]
    positivity
  have hB₂ : (B₂.card : ℝ) ≤ (X.card : ℝ) / 4 := by
    have ht : (B₂.card : ℝ) * (4 * R) ≤ (X.card : ℝ) * R := by
      calc
        _ = ∑ S ∈ B₂, (4 * R) := by simp
        _ ≤ ∑ S ∈ B₂, E S := Finset.sum_le_sum (fun S hS ↦ (Finset.mem_filter.mp hS).2.le)
        _ ≤ ∑ S ∈ X, E S := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun S _ _ ↦ Finset.sum_nonneg (fun i _ ↦ sq_nonneg _))
        _ ≤ _ := by
          rw [hcount]
          exact sum_sample_row_drift_energy_le s q hk hks p d η hq hd hη
    exact (le_of_mul_le_mul_right (show (B₂.card : ℝ) * R ≤ (X.card : ℝ) / 4 * R
      by linarith only [ht]) hR)
  have hCover : X ⊆ G ∪ (B₁ ∪ B₂) := by
    intro S hS
    by_cases hi : ∀ i ∈ S, |sampleRowDrift S q d i| ≤ t
    · by_cases hE : E S ≤ 4 * R
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hS, hi, hE⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr
          (Or.inr (Finset.mem_filter.mpr ⟨hS, lt_of_not_ge hE⟩))))
    · push Not at hi
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr
        (Or.inl (Finset.mem_filter.mpr ⟨hS, hi⟩))))
  have htotal : (X.card : ℝ) ≤ G.card + B₁.card + B₂.card := by
    have h := (Finset.card_le_card hCover).trans (Finset.card_union_le _ _)
    have hh : X.card ≤ G.card + B₁.card + B₂.card := by
      have hn := Finset.card_union_le B₁ B₂
      omega
    exact_mod_cast hh
  have he : 4 * R = 8 * (k : ℝ) ^ 2 + 8 * η ^ 2 * (k : ℝ) ^ 3 := by dsimp only [R]; ring
  change (s.card.choose k : ℝ) / 2 ≤ ((X.filter (fun S ↦
    (∀ i ∈ S, |sampleRowDrift S q d i| ≤ t) ∧
    E S ≤ 8 * (k : ℝ) ^ 2 + 8 * η ^ 2 * (k : ℝ) ^ 3)).card : ℝ)
  rw [← he, ← hcount]
  change (X.card : ℝ) / 2 ≤ (G.card : ℝ)
  linarith only [hB₁, hB₂, htotal]

end BoundedEdgeRegularSubgraphs
