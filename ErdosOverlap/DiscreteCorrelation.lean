/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.DiscreteDensity
public import ErdosOverlap.DiscreteTent

/-! # Exact correlation of the finite partition embedding

The integer difference count uses the original convention `a-b=k`.
The physical correlation at shift `t` therefore samples the opposite
signed difference at the grid points `t=kδ`.
-/

@[expose] public section

namespace ErdosOverlap.Discrete

open MeasureTheory Set

noncomputable section

def differenceCount (A B : Finset ℤ) (k : ℤ) : ℕ :=
  ((A ×ˢ B).filter (fun p => p.1-p.2=k)).card

def maximumCount (A B : Finset ℤ) : ℕ :=
  (A ×ˢ B).sup (fun p => differenceCount A B (p.1-p.2))

theorem differenceCount_le_card_left (A B : Finset ℤ) (k : ℤ) :
    differenceCount A B k ≤ A.card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro p hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  · intro p hp q hq hpq
    apply Prod.ext hpq
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    omega

theorem differenceCount_le_maximumCount (A B : Finset ℤ) (k : ℤ) :
    differenceCount A B k ≤ maximumCount A B := by
  by_cases hzero : differenceCount A B k = 0
  · simp [hzero]
  · have hn : ((A ×ˢ B).filter (fun p => p.1-p.2=k)).Nonempty :=
      Finset.card_ne_zero.mp hzero
    obtain ⟨p,hp⟩ := hn
    obtain ⟨hp,hpk⟩ := Finset.mem_filter.mp hp
    have h := Finset.le_sup (f := fun p => differenceCount A B (p.1-p.2)) hp
    simpa only [maximumCount, hpk] using h

theorem maximumCount_le_card_left (A B : Finset ℤ) : maximumCount A B ≤ A.card := by
  apply Finset.sup_le
  intro p _
  exact differenceCount_le_card_left A B _

theorem maximumCount_attained {A B : Finset ℤ} (hA : A.Nonempty) (hB : B.Nonempty) :
    ∃ k : ℤ, maximumCount A B = differenceCount A B k := by
  obtain ⟨p,hp,he⟩ := Finset.exists_mem_eq_sup (A ×ˢ B)
    (hA.product hB) (fun p => differenceCount A B (p.1-p.2))
  exact ⟨p.1-p.2,he⟩

theorem indexedCell_product_integrable (δ : ℝ) (a b : ℤ) (t : ℝ) :
    Integrable (fun x : ℝ => indexedCell δ a x * indexedCell δ b (x+t)) := by
  simp only [indexedCell_eq_intervalCell]
  exact intervalCell_product_integrable δ _ _ t

theorem indexedCell_correlation (δ : ℝ) (a b : ℤ) (t : ℝ) :
    (∫ x : ℝ, indexedCell δ a x * indexedCell δ b (x+t)) =
      max (δ - |t-((b-a : ℤ) : ℝ)*δ|) 0 := by
  simp only [indexedCell_eq_intervalCell]
  rw [intervalCell_correlation]
  congr 3
  push_cast
  ring

theorem density_product_eq_sum (δ : ℝ) (A B : Finset ℤ) (x t : ℝ) :
    density δ A x * density δ B (x+t) =
      ∑ a ∈ A, ∑ b ∈ B, indexedCell δ a x * indexedCell δ b (x+t) := by
  simp only [density, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

theorem density_product_integrable (δ : ℝ) (A B : Finset ℤ) (t : ℝ) :
    Integrable (fun x : ℝ => density δ A x * density δ B (x+t)) := by
  simp_rw [density_product_eq_sum]
  exact integrable_finsetSum A (fun a _ =>
    integrable_finsetSum B (fun b _ => indexedCell_product_integrable δ a b t))

theorem density_correlation (δ : ℝ) (A B : Finset ℤ) (t : ℝ) :
    (∫ x : ℝ, density δ A x * density δ B (x+t)) =
      ∑ a ∈ A, ∑ b ∈ B, max (δ-|t-((b-a : ℤ) : ℝ)*δ|) 0 := by
  simp_rw [density_product_eq_sum]
  rw [integral_finsetSum A (fun a _ =>
    integrable_finsetSum B (fun b _ => indexedCell_product_integrable δ a b t))]
  apply Finset.sum_congr rfl
  intro a ha
  rw [integral_finsetSum B (fun b _ => indexedCell_product_integrable δ a b t)]
  exact Finset.sum_congr rfl (fun b _ => indexedCell_correlation δ a b t)

theorem sum_difference_indicator (A B : Finset ℤ) (k : ℤ) (w : ℝ) :
    (∑ a ∈ A, ∑ b ∈ B, if a-b=k then w else 0) =
      (differenceCount A B k : ℝ)*w := by
  rw [← Finset.sum_product A B (fun p => if p.1-p.2=k then w else 0),
    ← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, differenceCount]

theorem sum_lag_indicator (A B : Finset ℤ) (k : ℤ) (w : ℝ) :
    (∑ a ∈ A, ∑ b ∈ B, if b-a=k then w else 0) =
      (differenceCount A B (-k) : ℝ)*w := by
  have he : ∀ a b : ℤ, (b-a=k) ↔ (a-b = -k) := by intros; omega
  simp_rw [he]
  exact sum_difference_indicator A B (-k) w

/-- The physical overlap is exactly affine between adjacent grid shifts. -/
theorem density_correlation_interpolation {δ : ℝ} (hδ : 0 < δ)
    (A B : Finset ℤ) (k : ℤ) (t : ℝ)
    (hl : (k : ℝ)*δ ≤ t) (hu : t ≤ ((k+1 : ℤ) : ℝ)*δ) :
    (∫ x : ℝ, density δ A x * density δ B (x+t)) =
      (differenceCount A B (-k) : ℝ)*(((k+1 : ℤ) : ℝ)*δ-t) +
      (differenceCount A B (-(k+1)) : ℝ)*(t-(k : ℝ)*δ) := by
  rw [density_correlation]
  simp_rw [integer_grid_tent δ hδ k _ t hl hu]
  simp only [Finset.sum_add_distrib]
  rw [sum_lag_indicator, sum_lag_indicator]

theorem density_correlation_at_grid {δ : ℝ} (hδ : 0 < δ)
    (A B : Finset ℤ) (k : ℤ) :
    (∫ x : ℝ, density δ A x * density δ B (x+(k : ℝ)*δ)) =
      (differenceCount A B (-k) : ℝ)*δ := by
  have hu : (k : ℝ)*δ ≤ ((k+1 : ℤ) : ℝ)*δ := by
    push_cast
    nlinarith
  rw [density_correlation_interpolation hδ A B k _ le_rfl hu]
  push_cast
  ring

theorem density_correlation_le_maximumCount {δ : ℝ} (hδ : 0 < δ)
    (A B : Finset ℤ) (t : ℝ) :
    (∫ x : ℝ, density δ A x * density δ B (x+t)) ≤
      (maximumCount A B : ℝ)*δ := by
  let k : ℤ := ⌊t/δ⌋
  have hl : (k : ℝ)*δ ≤ t := (le_div_iff₀ hδ).mp (Int.floor_le (t/δ))
  have hu : t ≤ ((k+1 : ℤ) : ℝ)*δ := by
    have hf := (div_lt_iff₀ hδ).mp (Int.lt_floor_add_one (t/δ))
    simpa only [Int.cast_add, Int.cast_one] using hf.le
  rw [density_correlation_interpolation hδ A B k t hl hu]
  have hc₀ : (differenceCount A B (-k) : ℝ) ≤ (maximumCount A B : ℝ) := by
    exact_mod_cast differenceCount_le_maximumCount A B (-k)
  have hc₁ : (differenceCount A B (-(k+1)) : ℝ) ≤ (maximumCount A B : ℝ) := by
    exact_mod_cast differenceCount_le_maximumCount A B (-(k+1))
  calc
    _ ≤ (maximumCount A B : ℝ)*(((k+1 : ℤ) : ℝ)*δ-t) +
        (maximumCount A B : ℝ)*(t-(k : ℝ)*δ) :=
      add_le_add (mul_le_mul_of_nonneg_right hc₀ (sub_nonneg.mpr hu))
        (mul_le_mul_of_nonneg_right hc₁ (sub_nonneg.mpr hl))
    _ = (maximumCount A B : ℝ)*δ := by push_cast; ring

theorem density_overlapCap {N : ℕ} (hN : 0 < N) {A B : Finset ℤ}
    (hp : BalancedPartition N A B) :
    OverlapCap (density (cellWidth N) A) ((maximumCount A B : ℝ)/(N : ℝ)) := by
  have hall (t : ℝ) : wholeOverlap (density (cellWidth N) A) t ≤
      (maximumCount A B : ℝ)/(N : ℝ) := by
    rw [wholeOverlap_density hN hp t]
    simpa only [cellWidth, mul_one_div] using
      density_correlation_le_maximumCount (cellWidth_pos hN) A B t
  intro t ht
  constructor
  · simpa only [wholeOverlap_eq_positive _ ht] using hall t
  · simpa only [wholeOverlap_neg_eq_negative _ ht] using hall (-t)

/-- The embedded binary density has exactly the normalized finite maximum. -/
theorem density_overlapPeak_eq {N : ℕ} (hN : 0 < N) {A B : Finset ℤ}
    (hp : BalancedPartition N A B) :
    overlapPeak (density (cellWidth N) A) = (maximumCount A B : ℝ)/(N : ℝ) := by
  have hh := density_admissible hN hp.left_subset hp.card_left
  apply le_antisymm ((overlapPeak_le_iff hh _).mpr (density_overlapCap hN hp))
  have hA : A.Nonempty := Finset.card_pos.mp (by simpa only [hp.card_left] using hN)
  have hB : B.Nonempty := Finset.card_pos.mp (by simpa only [hp.card_right] using hN)
  obtain ⟨k,hk⟩ := maximumCount_attained hA hB
  have hv : wholeOverlap (density (cellWidth N) A) ((-k : ℤ)*cellWidth N) =
      (maximumCount A B : ℝ)/(N : ℝ) := by
    rw [wholeOverlap_density hN hp, density_correlation_at_grid (cellWidth_pos hN), neg_neg,
      ← hk, cellWidth, mul_one_div]
  rw [← hv]
  apply le_csSup (overlapValues_bddAbove hh)
  rw [overlapValues_eq_range_wholeOverlap]
  exact ⟨_, rfl⟩

/-- Every finite balanced partition obeys any proved continuous binary lower bound. -/
theorem erdosOverlapConstant_le_normalizedMaximum {N : ℕ} (hN : 0 < N)
    {A B : Finset ℤ} (hp : BalancedPartition N A B) :
    erdosOverlapConstant ≤ (maximumCount A B : ℝ)/(N : ℝ) := by
  rw [← density_overlapPeak_eq hN hp]
  apply csInf_le partitionPeaks_bddBelow
  exact ⟨density (cellWidth N) A,
    density_binaryAdmissible hN hp.left_subset hp.card_left, rfl⟩

end
end ErdosOverlap.Discrete
