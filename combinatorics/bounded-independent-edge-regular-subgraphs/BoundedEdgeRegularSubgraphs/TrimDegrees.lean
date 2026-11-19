module

public import BoundedEdgeRegularSubgraphs.Model
import BoundedEdgeRegularSubgraphs.MeanDrift
import Mathlib.Tactic

/-!
# Trimming vertices with atypical expected degrees
-/

@[expose] public section

open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
private theorem sum_sq_sub_vertexMean_le (y : α → ℝ) (c : ℝ) :
    (∑ i, (y i - vertexMean y) ^ 2) ≤ ∑ i, (y i - c) ^ 2 := by
  let D := vertexMean y - c
  have h (i : α) : (y i - c) ^ 2 =
      (y i - vertexMean y) ^ 2 + 2 * D * (y i - vertexMean y) + D ^ 2 := by
    dsimp only [D]
    ring
  simp_rw [h, Finset.sum_add_distrib, ← Finset.mul_sum, sum_sub_vertexMean, mul_zero, add_zero]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)

/-- The trimming stage of Lemma 5.2. The retained row sums can drop by at
most the number of deleted vertices. -/
theorem exists_trimmed_degree_bounds (d : α → ℝ) (c : ℝ) {η : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 16) (hm : 32 ≤ Fintype.card α)
    (hvar : (∑ i, (d i - c) ^ 2) ≤ η ^ 2 * (Fintype.card α : ℝ) ^ 3) :
    ∃ S : Finset α, (15 / 16 : ℝ) * Fintype.card α ≤ (S.card : ℝ) ∧
      ∀ y : ↥S → ℝ, (∀ i : ↥S, d i - y i ∈ Set.Icc 0 ((Fintype.card α : ℝ) - S.card)) →
        (∀ i, |y i - vertexMean y| ≤ 3 * Real.sqrt η * ((S.card : ℝ) - 1)) ∧
        (∑ i, (y i - vertexMean y) ^ 2) / (S.card : ℝ) ≤
          6 * η ^ 2 * ((S.card : ℝ) - 1) ^ 2 := by
  classical
  let M : ℝ := Fintype.card α
  let S : Finset α := Finset.univ.filter fun i ↦ |d i - c| ≤ Real.sqrt η * M
  let T : Finset α := Finset.univ \ S
  let N : ℝ := S.card
  have hM : (32 : ℝ) ≤ M := by dsimp only [M]; exact_mod_cast hm
  have hM₀ : 0 < M := by linarith only [hM]
  have hN₀ : 0 ≤ N := Nat.cast_nonneg _
  have hT : (T.card : ℝ) + N = M := by
    dsimp only [T, M, N]
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
    rw [Finset.card_univ] at h
    exact_mod_cast h
  have hηs : Real.sqrt η ^ 2 = η := Real.sq_sqrt hη.le
  have hηs₀ : 0 ≤ Real.sqrt η := Real.sqrt_nonneg _
  have hbad (i : α) (hi : i ∈ T) : η * M ^ 2 ≤ (d i - c) ^ 2 := by
    have hh : Real.sqrt η * M ≤ |d i - c| := by
      have h := (Finset.mem_sdiff.mp hi).2
      exact le_of_lt (lt_of_not_ge (fun hi ↦ h (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)))
    have h := pow_le_pow_left₀ (mul_nonneg hηs₀ hM₀.le) hh 2
    simpa only [mul_pow, hηs, sq_abs] using h
  have hcard : (T.card : ℝ) ≤ η * M := by
    have hleft : (T.card : ℝ) * (η * M ^ 2) ≤ ∑ i ∈ T, (d i - c) ^ 2 := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum hbad
    have hright := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
      (fun i _ _ ↦ sq_nonneg (d i - c))
    have h := hleft.trans (hright.trans hvar)
    apply le_of_mul_le_mul_right _ (show 0 < η * M ^ 2 by positivity)
    linarith only [h]
  have hN : (15 / 16 : ℝ) * M ≤ N := by
    have h := mul_le_mul_of_nonneg_right hη' hM₀.le
    linarith only [hcard, hT, h]
  have hN₁ : (7 / 8 : ℝ) * M ≤ N - 1 := by linarith only [hN, hM]
  have hNpos : 0 < N := by linarith only [hN, hM]
  have hNM : N ≤ M := (Nat.cast_le.mpr (Finset.card_le_univ S))
  refine ⟨S, hN, ?_⟩
  intro y hy
  have hret (i : ↥S) : |d i - c| ≤ Real.sqrt η * M :=
    (Finset.mem_filter.mp i.property).2
  have hd (i : ↥S) : |y i - d i| ≤ η * M := by
    rw [abs_sub_comm, abs_of_nonneg (hy i).1]
    linarith only [(hy i).2, hT, hcard]
  let B := (Real.sqrt η + η) * M
  have hbefore (i : ↥S) : |y i - c| ≤ B := by
    have h := (abs_sub_le (y i) (d i) c).trans (add_le_add (hd i) (hret i))
    dsimp only [B]
    linarith only [h]
  have hmean : |vertexMean y - c| ≤ B := by
    have hE : vertexMean y - c = (∑ i, (y i - c)) / N := by
      unfold vertexMean
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_coe]
      change (∑ i, y i) / N - c = _
      field_simp
      change _ - (S.card : ℝ) * c = _
      ring
    rw [hE, abs_div, abs_of_nonneg hN₀]
    apply (div_le_iff₀ hNpos).2
    calc
      _ ≤ ∑ i : ↥S, |y i - c| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : ↥S, B := Finset.sum_le_sum (fun i _ ↦ hbefore i)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_coe, N]; ring
  constructor
  · have hs₁ : Real.sqrt η ≤ 1 / 4 := by
      rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 1 / 4)]
      norm_num
      exact hη'
    have hη₁ : η ≤ Real.sqrt η / 4 := by
      nlinarith only [hηs, mul_le_mul_of_nonneg_left hs₁ hηs₀]
    intro i
    have h : |y i - vertexMean y| ≤ B + B := (abs_sub_le (y i) c (vertexMean y)).trans
      (add_le_add (hbefore i) (by rw [abs_sub_comm c]; exact hmean))
    have hl := mul_le_mul_of_nonneg_right hη₁ hM₀.le
    have hr := mul_le_mul_of_nonneg_left hN₁ hηs₀
    dsimp only [B] at h
    change _ ≤ 3 * Real.sqrt η * (N - 1)
    linarith only [h, hl, hr, mul_nonneg hηs₀ hM₀.le]
  · have hsq (i : ↥S) : (y i - c) ^ 2 ≤
        2 * (d i - c) ^ 2 + 2 * (η * M) ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg _) (hd i) 2
      rw [sq_abs] at h
      nlinarith only [h, sq_nonneg (y i - d i - (d i - c))]
    have htotal : (∑ i : ↥S, (d i - c) ^ 2) ≤ η ^ 2 * M ^ 3 := by
      rw [Finset.sum_coe_sort S (fun i ↦ (d i - c) ^ 2)]
      exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        (fun i _ _ ↦ sq_nonneg (d i - c))).trans hvar
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hsq i)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul,
      Finset.card_univ, Fintype.card_coe] at hsum
    change _ ≤ 2 * (∑ i : ↥S, (d i - c) ^ 2) + N * (2 * (η * M) ^ 2) at hsum
    have htot : (∑ i : ↥S, (y i - c) ^ 2) ≤ 4 * η ^ 2 * M ^ 3 := by
      have h := mul_le_mul_of_nonneg_right hNM (show 0 ≤ 2 * (η * M) ^ 2 by positivity)
      linarith only [hsum, htotal, h]
    have hcent := (sum_sq_sub_vertexMean_le y c).trans htot
    change (∑ i, (y i - vertexMean y) ^ 2) / N ≤ 6 * η ^ 2 * (N - 1) ^ 2
    apply (div_le_iff₀ hNpos).2
    refine hcent.trans ?_
    have hs₁ := pow_le_pow_left₀ (show 0 ≤ (7 / 8 : ℝ) * M by positivity) hN₁ 2
    have hh := mul_le_mul hN hs₁ (by positivity) hN₀
    have ht := mul_le_mul_of_nonneg_left hh (show 0 ≤ 6 * η ^ 2 by positivity)
    have hn : 0 ≤ η ^ 2 * M ^ 3 := by positivity
    linarith only [ht, hn]

end BoundedEdgeRegularSubgraphs
