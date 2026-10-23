/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.SparseCompletion

@[expose] public section

open scoped BigOperators

namespace SparseCompletion
noncomputable section

def lowerPositive {ι : Type*} (a : ℝ) (y : ι → ℝ) (i : ι) : ℝ := by
  classical
  exact if 0 < y i then y i-a else 0

def positiveSet {ι : Type*} [Fintype ι] (y : ι → ℝ) : Finset ι := by
  classical
  exact Finset.univ.filter fun i => 0 < y i

def weightedVariation {ι : Type*} [Fintype ι] (q y : ι → ℝ) : ℝ :=
  (∑ i, ∑ j, q i*q j*|y i-y j|)/(2 : ℕ)

theorem masked_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (s : Finset ι) (f : ι → ℝ) :
    (∑ i, if i ∈ s then f i else 0) = mass s f := by
  unfold mass
  calc
    _ = ∑ i ∈ s, if i ∈ s then f i else 0 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro i _ hi
      exact ite_eq_right hi
    _ = _ := Finset.sum_congr rfl fun i hi => ite_eq_left hi

theorem complement_masked_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (q : ι → ℝ) (r : ℝ) (hr : ∑ i, q i = r) :
    (∑ i, if i ∈ s then 0 else q i) = r-mass s q := by
  have heq : (∑ i, if i ∈ s then q i else 0)+(∑ i, if i ∈ s then 0 else q i) = r := by
    rw [← Finset.sum_add_distrib, ← hr]
    exact Finset.sum_congr rfl fun i _ => by split <;> simp_all
  rw [masked_sum] at heq
  linarith

theorem outer_product_sum {ι : Type*} [Fintype ι] (f g : ι → ℝ) :
    (∑ i, ∑ j, f i*g j) = (∑ i, f i)*(∑ j, g j) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]

theorem positive_pair_decomposition {ι : Type*} (a : ℝ) (q y : ι → ℝ)
    (hy : ∀ i, 0 ≤ y i) (hmin : ∀ i, 0 < y i → a ≤ y i) (i j : ι) :
    q i*q j*|y i-y j| = q i*q j*|lowerPositive a y i-lowerPositive a y j| +
      a*((if 0 < y i then q i else 0)*(if 0 < y j then 0 else q j)+
         (if 0 < y i then 0 else q i)*(if 0 < y j then q j else 0)) := by
  classical
  by_cases hi : 0 < y i <;> by_cases hj : 0 < y j
  · simp only [lowerPositive, ite_eq_left hi, ite_eq_left hj, mul_zero, zero_mul, add_zero]
    congr 2
    ring
  · have hj0 : y j = 0 := by linarith [hy j]
    have hia : 0 ≤ y i-a := by linarith [hmin i hi]
    simp [lowerPositive, hi, hj0, abs_of_nonneg (hy i), abs_of_nonneg hia]
    ring
  · have hi0 : y i = 0 := by linarith [hy i]
    have hja : y j-a ≥ 0 := by linarith [hmin j hj]
    simp only [lowerPositive, ite_eq_right hi, ite_eq_left hj]
    rw [hi0]
    simp only [zero_sub, abs_neg, abs_of_nonneg (hy j), abs_of_nonneg hja,
      mul_zero]
    ring
  · have hi0 : y i = 0 := by linarith [hy i]
    have hj0 : y j = 0 := by linarith [hy j]
    simp [lowerPositive, hi0, hj0]

theorem variation_lower_positive {ι : Type*} [Fintype ι]
    (a : ℝ) (q y : ι → ℝ) (r : ℝ) (hr : ∑ i, q i = r)
    (hy : ∀ i, 0 ≤ y i) (hmin : ∀ i, 0 < y i → a ≤ y i) :
    weightedVariation q y = weightedVariation q (lowerPositive a y)+
      a*mass (positiveSet y) q*(r-mass (positiveSet y) q) := by
  classical
  let s := positiveSet y
  let f : ι → ℝ := fun i => if i ∈ s then q i else 0
  let g : ι → ℝ := fun i => if i ∈ s then 0 else q i
  have hf : ∑ i, f i = mass s q := masked_sum s q
  have hg : ∑ i, g i = r-mass s q := complement_masked_sum s q r hr
  have hp : ∀ i j, q i*q j*|y i-y j| = q i*q j*|lowerPositive a y i-lowerPositive a y j|+
      a*(f i*g j+g i*f j) := by
    intro i j
    simpa only [f, g, s, positiveSet, Finset.mem_filter, Finset.mem_univ, true_and] using
      positive_pair_decomposition a q y hy hmin i j
  have hcross : (∑ i, ∑ j, a*(f i*g j+g i*f j)) =
      a*((∑ i, f i)*(∑ j, g j)+(∑ i, g i)*(∑ j, f j)) := by
    simp only [← Finset.mul_sum, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, ← Finset.sum_mul]
  have hsum : (∑ i, ∑ j, q i*q j*|y i-y j|) =
      (∑ i, ∑ j, q i*q j*|lowerPositive a y i-lowerPositive a y j|)+
      a*((∑ i, f i)*(∑ j, g j)+(∑ i, g i)*(∑ j, f j)) := by
    simp_rw [hp]
    simp only [Finset.sum_add_distrib]
    rw [hcross]
  rw [hf, hg] at hsum
  unfold weightedVariation
  dsimp [s] at hsum
  linarith

theorem demand_lower_positive {ι : Type*} [Fintype ι]
    (a : ℝ) (q v y : ι → ℝ) (hy : ∀ i, 0 ≤ y i) :
    (∑ i, q i*v i*y i) = (∑ i, q i*v i*lowerPositive a y i)+
      a*(∑ i ∈ positiveSet y, q i*v i) := by
  classical
  have hp : ∀ i, q i*v i*y i = q i*v i*lowerPositive a y i+
      a*(if i ∈ positiveSet y then q i*v i else 0) := by
    intro i
    by_cases hi : 0 < y i
    · simp only [lowerPositive, positiveSet, Finset.mem_filter,
        Finset.mem_univ, true_and, ite_eq_left hi]
      ring
    · have hi0 : y i = 0 := by linarith [hy i]
      simp [lowerPositive, positiveSet, hi0]
  simp_rw [hp]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, masked_sum]
  rfl

/-- Finite layer-cake extension of all subset cuts to every nonnegative
    linear test vector. No separation or completion theorem is assumed. -/
theorem cuts_dual_bound {ι : Type*} [Fintype ι]
    (q v : ι → ℝ) (M r : ℝ) (hr : ∑ i, q i = r) (hc : Cuts M r q v)
    (y : ι → ℝ) (hy : ∀ i, 0 ≤ y i) :
    (∑ i, q i*v i*y i) ≤ M*weightedVariation q y := by
  classical
  by_cases hs : (positiveSet y).Nonempty
  · let s := positiveSet y
    let t := s.image y
    have ht : t.Nonempty := hs.image y
    let a := t.min' ht
    have hamem : a ∈ t := Finset.min'_mem t ht
    obtain ⟨i, hi, hai⟩ := Finset.mem_image.mp hamem
    have ha : 0 < a := by
      rw [← hai]
      exact (Finset.mem_filter.mp hi).2
    have hmin : ∀ j, 0 < y j → a ≤ y j := by
      intro j hj
      apply Finset.min'_le
      exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩, rfl⟩
    have hnonneg : ∀ j, 0 ≤ lowerPositive a y j := by
      intro j
      dsimp [lowerPositive]
      split
      · rename_i hj
        linarith [hmin j hj]
      · exact le_rfl
    have hsub : positiveSet (lowerPositive a y) ⊆ s.erase i := by
      intro j hj
      have hjpos : 0 < lowerPositive a y j := (Finset.mem_filter.mp hj).2
      have hjy : 0 < y j := by
        by_contra hn
        simp only [lowerPositive, ite_eq_right hn] at hjpos
        linarith
      have hji : j ≠ i := by
        intro he
        subst j
        simp [lowerPositive, hai, ha] at hjpos
      exact Finset.mem_erase.mpr ⟨hji, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjy⟩⟩
    have hcard : (positiveSet (lowerPositive a y)).card < (positiveSet y).card :=
      lt_of_le_of_lt (Finset.card_le_card hsub) (Finset.card_erase_lt_of_mem hi)
    have ih := cuts_dual_bound q v M r hr hc (lowerPositive a y) hnonneg
    calc
      _ = (∑ j, q j*v j*lowerPositive a y j)+a*(∑ j ∈ positiveSet y, q j*v j) :=
        demand_lower_positive a q v y hy
      _ ≤ M*weightedVariation q (lowerPositive a y)+a*(M*mass (positiveSet y) q*(r-mass (positiveSet y) q)) :=
        add_le_add ih (mul_le_mul_of_nonneg_left (hc (positiveSet y)) (le_of_lt ha))
      _ = _ := by
        rw [variation_lower_positive a q y r hr hy hmin]
        ring
  · have hy0 : ∀ i, y i = 0 := by
      intro i
      have hn : ¬0 < y i := by
        intro hi
        exact hs ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
      linarith [hy i]
    simp only [hy0, mul_zero, Finset.sum_const_zero, weightedVariation, sub_self, abs_zero, zero_div, le_refl]
termination_by (positiveSet y).card
decreasing_by exact hcard

end
end SparseCompletion
