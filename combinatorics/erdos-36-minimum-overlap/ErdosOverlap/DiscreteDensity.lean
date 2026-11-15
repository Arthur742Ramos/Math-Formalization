/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.IntervalCell
public import ErdosOverlap.Constant
public import Mathlib.Algebra.Order.Floor.Ring

/-!
# Embedding a finite balanced partition into interval cells

Integer label `j` is represented by the half-open cell `[(j-1)δ,jδ)`.
Distinct labels give disjoint cells. At `δ=1/N`, a subset of `{1,…,2N}`
with `N` elements is an actual binary admissible density on `[0,2]`.
-/

@[expose] public section

namespace ErdosOverlap.Discrete

open MeasureTheory Set
open scoped Interval

noncomputable section

def cellSet (δ : ℝ) (j : ℤ) : Set ℝ := Ico (((j : ℝ)-1)*δ) ((j : ℝ)*δ)

def indexedCell (δ : ℝ) (j : ℤ) : ℝ → ℝ :=
  (cellSet δ j).indicator (fun _ => 1)

theorem indexedCell_eq_intervalCell (δ : ℝ) (j : ℤ) :
    indexedCell δ j = intervalCell δ (((j : ℝ)-1)*δ) := by
  unfold indexedCell cellSet intervalCell
  rw [show ((j : ℝ)-1)*δ+δ = (j : ℝ)*δ by ring]

def density (δ : ℝ) (A : Finset ℤ) (x : ℝ) : ℝ :=
  ∑ j ∈ A, indexedCell δ j x

theorem indexedCell_measurable (δ : ℝ) (j : ℤ) : Measurable (indexedCell δ j) :=
  measurable_const.indicator measurableSet_Ico

theorem indexedCell_integrable (δ : ℝ) (j : ℤ) : Integrable (indexedCell δ j) := by
  rw [indexedCell_eq_intervalCell]
  exact intervalCell_integrable δ _

theorem integral_indexedCell (δ : ℝ) (j : ℤ) (hδ : 0 ≤ δ) :
    (∫ x : ℝ, indexedCell δ j x) = δ := by
  rw [indexedCell_eq_intervalCell]
  exact integral_intervalCell δ _ hδ

theorem cellSet_unique {δ x : ℝ} (hδ : 0 < δ) {i j : ℤ}
    (hi : x ∈ cellSet δ i) (hj : x ∈ cellSet δ j) : i = j := by
  have hji : (j : ℝ)-1 < (i : ℝ) :=
    (mul_lt_mul_iff_left₀ hδ).mp (hj.1.trans_lt hi.2)
  have hij : (i : ℝ)-1 < (j : ℝ) :=
    (mul_lt_mul_iff_left₀ hδ).mp (hi.1.trans_lt hj.2)
  have hji' : j-1 < i := by exact_mod_cast hji
  have hij' : i-1 < j := by exact_mod_cast hij
  omega

theorem density_eq_one_of_mem {δ x : ℝ} (hδ : 0 < δ) {A : Finset ℤ} {j : ℤ}
    (hj : j ∈ A) (hx : x ∈ cellSet δ j) : density δ A x = 1 := by
  unfold density
  rw [Finset.sum_eq_single j]
  · simp [indexedCell, hx]
  · intro i hi hij
    have hnot : x ∉ cellSet δ i := fun hxi => hij (cellSet_unique hδ hxi hx)
    simp [indexedCell, hnot]
  · intro hn
    exact (hn hj).elim

theorem density_binary {δ : ℝ} (hδ : 0 < δ) (A : Finset ℤ) (x : ℝ) :
    density δ A x = 0 ∨ density δ A x = 1 := by
  by_cases hx : ∃ j ∈ A, x ∈ cellSet δ j
  · obtain ⟨j,hj,hxj⟩ := hx
    exact Or.inr (density_eq_one_of_mem hδ hj hxj)
  · left
    apply Finset.sum_eq_zero
    intro j hj
    have hnot : x ∉ cellSet δ j := fun h => hx ⟨j,hj,h⟩
    simp [indexedCell, hnot]

theorem density_nonneg {δ : ℝ} (hδ : 0 < δ) (A : Finset ℤ) (x : ℝ) :
    0 ≤ density δ A x := by
  rcases density_binary hδ A x with h | h <;> simp [h]

theorem density_le_one {δ : ℝ} (hδ : 0 < δ) (A : Finset ℤ) (x : ℝ) :
    density δ A x ≤ 1 := by
  rcases density_binary hδ A x with h | h <;> simp [h]

theorem density_measurable (δ : ℝ) (A : Finset ℤ) : Measurable (density δ A) := by
  unfold density
  exact Finset.measurable_sum _ (fun j _ => indexedCell_measurable δ j)

theorem density_integrable (δ : ℝ) (A : Finset ℤ) : Integrable (density δ A) := by
  exact integrable_finsetSum A (fun j _ => indexedCell_integrable δ j)

theorem integral_density {δ : ℝ} (hδ : 0 ≤ δ) (A : Finset ℤ) :
    (∫ x : ℝ, density δ A x) = (A.card : ℝ)*δ := by
  unfold density
  rw [integral_finsetSum A (fun j _ => indexedCell_integrable δ j)]
  simp only [integral_indexedCell δ _ hδ, Finset.sum_const, nsmul_eq_mul]

theorem cellSet_subset_span {δ : ℝ} (hδ : 0 < δ) {j K : ℤ}
    (hj : j ∈ Finset.Icc 1 K) : cellSet δ j ⊆ Ico 0 ((K : ℝ)*δ) := by
  obtain ⟨hj0,hjK⟩ := Finset.mem_Icc.mp hj
  have hj0' : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj0
  have hjK' : (j : ℝ) ≤ (K : ℝ) := by exact_mod_cast hjK
  intro x hx
  exact ⟨(mul_nonneg (sub_nonneg.mpr hj0') hδ.le).trans hx.1,
    hx.2.trans_le (mul_le_mul_of_nonneg_right hjK' hδ.le)⟩

theorem density_eq_zero_off_span {δ : ℝ} (hδ : 0 < δ) {A : Finset ℤ} {K : ℤ}
    (hA : A ⊆ Finset.Icc 1 K) {x : ℝ} (hx : x ∉ Ico 0 ((K : ℝ)*δ)) :
    density δ A x = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  have hn : x ∉ cellSet δ j := fun hm => hx (cellSet_subset_span hδ (hA hj) hm)
  simp [indexedCell, hn]

theorem density_indicator_span {δ : ℝ} (hδ : 0 < δ) {A : Finset ℤ} {K : ℤ}
    (hA : A ⊆ Finset.Icc 1 K) :
    (Ico 0 ((K : ℝ)*δ)).indicator (density δ A) = density δ A := by
  funext x
  by_cases hx : x ∈ Ico 0 ((K : ℝ)*δ)
  · simp [hx]
  · simp [hx, density_eq_zero_off_span hδ hA hx]

theorem intervalIntegral_density_span {δ : ℝ} (hδ : 0 < δ) {A : Finset ℤ} {K : ℤ}
    (hK : 0 ≤ K) (hA : A ⊆ Finset.Icc 1 K) :
    (∫ x in (0 : ℝ)..((K : ℝ)*δ), density δ A x) = (A.card : ℝ)*δ := by
  have hK' : (0 : ℝ) ≤ (K : ℝ)*δ :=
    mul_nonneg (by exact_mod_cast hK) hδ.le
  rw [intervalIntegral.integral_of_le hK', ← integral_Ico_eq_integral_Ioc,
    ← integral_indicator measurableSet_Ico, density_indicator_span hδ hA]
  exact integral_density hδ.le A

def cellWidth (N : ℕ) : ℝ := 1/(N : ℝ)

theorem cellWidth_pos {N : ℕ} (hN : 0 < N) : 0 < cellWidth N :=
  one_div_pos.mpr (by exact_mod_cast hN)

theorem cellWidth_span {N : ℕ} (hN : 0 < N) :
    ((2*(N : ℤ) : ℤ) : ℝ)*cellWidth N = 2 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hN)
  simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, cellWidth]
  field_simp

/-- A literal finite equal-size partition of the first `2N` positive integers. -/
structure BalancedPartition (N : ℕ) (A B : Finset ℤ) : Prop where
  disjoint : Disjoint A B
  union : A ∪ B = Finset.Icc 1 (2*(N : ℤ))
  card_left : A.card = N
  card_right : B.card = N

theorem BalancedPartition.left_subset {N : ℕ} {A B : Finset ℤ}
    (hp : BalancedPartition N A B) : A ⊆ Finset.Icc 1 (2*(N : ℤ)) := by
  intro a ha
  rw [← hp.union]
  exact Finset.mem_union_left _ ha

theorem BalancedPartition.right_subset {N : ℕ} {A B : Finset ℤ}
    (hp : BalancedPartition N A B) : B ⊆ Finset.Icc 1 (2*(N : ℤ)) := by
  intro b hb
  rw [← hp.union]
  exact Finset.mem_union_right _ hb

theorem density_admissible {N : ℕ} (hN : 0 < N) {A : Finset ℤ}
    (hA : A ⊆ Finset.Icc 1 (2*(N : ℤ))) (hcard : A.card = N) :
    Admissible (density (cellWidth N) A) where
  measurable := density_measurable _ _
  nonneg := fun x _ => density_nonneg (cellWidth_pos hN) A x
  le_one := fun x _ => density_le_one (cellWidth_pos hN) A x
  mass := by
    have hi := intervalIntegral_density_span (cellWidth_pos hN)
      (by positivity : (0 : ℤ) ≤ 2*(N : ℤ)) hA
    rw [cellWidth_span hN, hcard] at hi
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hN)
    simpa only [cellWidth, mul_one_div_cancel hn] using hi

theorem density_binaryAdmissible {N : ℕ} (hN : 0 < N) {A : Finset ℤ}
    (hA : A ⊆ Finset.Icc 1 (2*(N : ℤ))) (hcard : A.card = N) :
    BinaryAdmissible (density (cellWidth N) A) :=
  ⟨density_admissible hN hA hcard, fun x _ => density_binary (cellWidth_pos hN) A x⟩

theorem exists_cellSet_of_mem_span {δ x : ℝ} (hδ : 0 < δ) {K : ℤ}
    (hx : x ∈ Ico 0 ((K : ℝ)*δ)) :
    ∃ j ∈ Finset.Icc 1 K, x ∈ cellSet δ j := by
  refine ⟨⌊x/δ⌋+1, ?_, ?_⟩
  · apply Finset.mem_Icc.mpr
    have hfloor0 : (0 : ℤ) ≤ ⌊x/δ⌋ :=
      Int.floor_nonneg.mpr (div_nonneg hx.1 hδ.le)
    have hfloorK : ⌊x/δ⌋ < K := Int.floor_lt.mpr ((div_lt_iff₀ hδ).mpr hx.2)
    omega
  · change (((⌊x/δ⌋+1 : ℤ) : ℝ)-1)*δ ≤ x ∧
      x < ((⌊x/δ⌋+1 : ℤ) : ℝ)*δ
    simp only [Int.cast_add, Int.cast_one, add_sub_cancel_right]
    exact ⟨(le_div_iff₀ hδ).mp (Int.floor_le (x/δ)),
      (div_lt_iff₀ hδ).mp (Int.lt_floor_add_one (x/δ))⟩

theorem density_grid {δ : ℝ} (hδ : 0 < δ) (K : ℤ) (x : ℝ) :
    density δ (Finset.Icc 1 K) x = (Ico 0 ((K : ℝ)*δ)).indicator (fun _ => 1) x := by
  by_cases hx : x ∈ Ico 0 ((K : ℝ)*δ)
  · obtain ⟨j,hj,hxj⟩ := exists_cellSet_of_mem_span hδ hx
    rw [density_eq_one_of_mem hδ hj hxj]
    simp [hx]
  · rw [density_eq_zero_off_span hδ (fun _ hi => hi) hx]
    simp [hx]

theorem density_union (δ : ℝ) {A B : Finset ℤ} (hAB : Disjoint A B) (x : ℝ) :
    density δ (A ∪ B) x = density δ A x+density δ B x := by
  exact Finset.sum_union hAB

theorem density_add_complement {N : ℕ} (hN : 0 < N) {A B : Finset ℤ}
    (hp : BalancedPartition N A B) {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 2) :
    density (cellWidth N) A x+density (cellWidth N) B x = 1 := by
  rw [← density_union _ hp.disjoint, hp.union, density_grid (cellWidth_pos hN), cellWidth_span hN]
  simp [hx]

theorem density_eq_zero_off_unit_span {N : ℕ} (hN : 0 < N) {A : Finset ℤ}
    (hA : A ⊆ Finset.Icc 1 (2*(N : ℤ))) {x : ℝ} (hx : x ∉ Ico (0 : ℝ) 2) :
    density (cellWidth N) A x = 0 := by
  apply density_eq_zero_off_span (cellWidth_pos hN) hA
  simpa only [cellWidth_span hN] using hx

theorem supportedDensity_density {N : ℕ} (hN : 0 < N) {A : Finset ℤ}
    (hA : A ⊆ Finset.Icc 1 (2*(N : ℤ))) :
    supportedDensity (density (cellWidth N) A) = density (cellWidth N) A := by
  funext x
  by_cases hx : x ∈ Icc (0 : ℝ) 2
  · simp [supportedDensity, hx]
  · have hn : x ∉ Ico (0 : ℝ) 2 := fun hm => hx ⟨hm.1,hm.2.le⟩
    simp [supportedDensity, hx, density_eq_zero_off_unit_span hN hA hn]

/-- The complement agrees with the other finite colour except possibly at
the endpoint `2`, which has Lebesgue measure zero. -/
theorem supportedComplement_density_ae {N : ℕ} (hN : 0 < N) {A B : Finset ℤ}
    (hp : BalancedPartition N A B) :
    supportedComplement (density (cellWidth N) A) =ᵐ[volume] density (cellWidth N) B := by
  filter_upwards [Measure.ae_ne volume (2 : ℝ)] with x hx2
  by_cases hx : x ∈ Icc (0 : ℝ) 2
  · have hxo : x ∈ Ico (0 : ℝ) 2 := ⟨hx.1, lt_of_le_of_ne hx.2 hx2⟩
    have hs := density_add_complement hN hp hxo
    simp only [supportedComplement, indicator_of_mem hx]
    linarith
  · have hn : x ∉ Ico (0 : ℝ) 2 := fun hm => hx ⟨hm.1,hm.2.le⟩
    simp [supportedComplement, hx, density_eq_zero_off_unit_span hN hp.right_subset hn]

theorem wholeOverlap_density {N : ℕ} (hN : 0 < N) {A B : Finset ℤ}
    (hp : BalancedPartition N A B) (t : ℝ) :
    wholeOverlap (density (cellWidth N) A) t =
      ∫ x : ℝ, density (cellWidth N) A x*density (cellWidth N) B (x+t) := by
  have hs := (measurePreserving_add_right volume t).quasiMeasurePreserving.ae
    (supportedComplement_density_ae hN hp)
  unfold wholeOverlap
  rw [supportedDensity_density hN hp.left_subset]
  apply integral_congr_ae
  filter_upwards [hs] with x hx
  rw [hx]

end
end ErdosOverlap.Discrete
