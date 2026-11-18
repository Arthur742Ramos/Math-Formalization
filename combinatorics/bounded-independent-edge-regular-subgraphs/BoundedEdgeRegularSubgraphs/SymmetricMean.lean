module

public import BoundedEdgeRegularSubgraphs.WeightedSubsets
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# The elementary symmetric mean for sampling without replacement
-/

public section

open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [DecidableEq α]

private def inclusionWeight (s : Finset α) (w : α → ℝ) (k : ℕ) (i : α) : ℝ :=
  ∑ t ∈ (s.powersetCard k).filter (fun t ↦ i ∈ t), ∏ x ∈ t, w x

private theorem inclusionWeight_mono (s : Finset α) (w : α → ℝ)
    (hw : ∀ x ∈ s, 0 ≤ w x) (k : ℕ) {i j : α}
    (hi : i ∈ s) (hj : j ∈ s) (hij : w i ≤ w j) :
    inclusionWeight s w k i ≤ inclusionWeight s w k j := by
  classical
  by_cases hne : i = j
  · subst j; rfl
  let E := Equiv.swap i j
  let F (t : Finset α) := t.map E.toEmbedding
  have hmem (x : α) (t : Finset α) : x ∈ F t ↔ E x ∈ t := by
    dsimp only [F]
    rw [Finset.mem_map_equiv]
    simp [E]
  have hmap (x : α) (hx : x ∈ s) : E x ∈ s := by
    by_cases hxi : x = i
    · subst x; simpa [E] using hj
    by_cases hxj : x = j
    · subst x; simpa [E] using hi
    simpa only [E, Equiv.swap_apply_of_ne_of_ne hxi hxj] using hx
  unfold inclusionWeight
  refine Finset.sum_le_sum_of_injOn F (Finset.map_injective _).injOn ?_ ?_ ?_
  · intro t ht
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hu', hiu⟩ := Finset.mem_filter.mp hu
    obtain ⟨hus, huk⟩ := Finset.mem_powersetCard.mp hu'
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powersetCard.mpr ⟨?_, by simpa [F] using huk⟩, ?_⟩
    · intro x hx
      have hx' := hmap (E x) (hus ((hmem x u).mp hx))
      simpa only [E, Equiv.swap_apply_self] using hx'
    · exact (hmem j u).mpr (by simpa [E] using hiu)
  · intro t ht
    obtain ⟨ht', hit⟩ := Finset.mem_filter.mp ht
    have hsub := (Finset.mem_powersetCard.mp ht').1
    by_cases hjt : j ∈ t
    · have hh : F t = t := by
        ext x
        rw [hmem]
        by_cases hxi : x = i
        · subst x; simp [E, hit, hjt]
        by_cases hxj : x = j
        · subst x; simp [E, hit, hjt]
        simp only [E, Equiv.swap_apply_of_ne_of_ne hxi hxj]
      rw [hh]
    · have hh : F t = insert j (t.erase i) := by
        ext x
        rw [hmem, Finset.mem_insert, Finset.mem_erase]
        by_cases hxi : x = i
        · subst x; simp [E, hjt, hne]
        by_cases hxj : x = j
        · subst x; simp [E, hit]
        simp [E, Equiv.swap_apply_of_ne_of_ne hxi hxj, hxi, hxj]
      have hnot : j ∉ t.erase i := fun h ↦ hjt (Finset.mem_of_mem_erase h)
      rw [hh, Finset.prod_insert hnot, ← Finset.prod_erase_mul t w hit, mul_comm (w j)]
      exact mul_le_mul_of_nonneg_left hij
        (Finset.prod_nonneg (fun x hx ↦ hw x (hsub (Finset.mem_of_mem_erase hx))))
  · intro t ht _
    have hsub := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp ht).1).1
    exact Finset.prod_nonneg (fun x hx ↦ hw x (hsub hx))

private theorem sum_inclusionWeight (s : Finset α) (w f : α → ℝ) (k : ℕ) :
    (∑ i ∈ s, inclusionWeight s w k i * f i) =
      ∑ t ∈ s.powersetCard k, (∏ x ∈ t, w x) * ∑ i ∈ t, f i := by
  classical
  unfold inclusionWeight
  simp_rw [Finset.sum_mul, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  have hts := (Finset.mem_powersetCard.mp ht).1
  rw [← Finset.sum_filter]
  have he : s.filter (fun i ↦ i ∈ t) = t := by
    ext i
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun h ↦ ⟨hts h, h⟩⟩
  rw [he, Finset.mul_sum]

private theorem weighted_subsets_next_le (s : Finset α) (w : α → ℝ)
    (hs : 0 < s.card) (hw : ∀ x ∈ s, 0 ≤ w x) (k : ℕ) :
    (k + 1 : ℝ) * (∑ t ∈ s.powersetCard (k + 1), ∏ x ∈ t, w x) ≤
      ((s.card : ℝ) - k) * ((∑ i ∈ s, w i) / s.card) *
        (∑ t ∈ s.powersetCard k, ∏ x ∈ t, w x) := by
  classical
  let U := s.powersetCard k
  let S := ∑ i ∈ s, w i
  let E := ∑ t ∈ U, ∏ x ∈ t, w x
  let A := ∑ t ∈ U, (∏ x ∈ t, w x) * ∑ i ∈ t, w i
  have hmono : MonovaryOn (inclusionWeight s w k) w s :=
    fun _ hi _ hj hij ↦ inclusionWeight_mono s w hw k hi hj hij.le
  have hcheb := hmono.sum_mul_sum_le_card_mul_sum
  have hid : (∑ i ∈ s, inclusionWeight s w k i) = (k : ℝ) * E := by
    have h := sum_inclusionWeight s w (fun _ ↦ 1) k
    simp only [mul_one, Finset.sum_const, nsmul_eq_mul] at h
    rw [h, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    rw [(Finset.mem_powersetCard.mp ht).2, mul_comm]
  rw [hid, sum_inclusionWeight] at hcheb
  change ((k : ℝ) * E) * S ≤ (s.card : ℝ) * A at hcheb
  have hrec : (k + 1 : ℝ) * (∑ t ∈ s.powersetCard (k + 1), ∏ x ∈ t, w x) =
      S * E - A := by
    rw [weighted_subsets_marked]
    dsimp only [S, E, A, U]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    have hts := (Finset.mem_powersetCard.mp ht).1
    rw [← Finset.sum_sdiff hts]
    ring
  rw [hrec]
  apply (le_of_mul_le_mul_left (a := (s.card : ℝ))) _ (Nat.cast_pos.mpr hs)
  field_simp [show (s.card : ℝ) ≠ 0 by positivity]
  nlinarith only [hcheb]

/-- The elementary symmetric mean is bounded by the corresponding power of
the arithmetic mean, including the normalization for distinct samples. -/
theorem sum_powersetCard_prod_le_choose_mean_pow (s : Finset α) (w : α → ℝ)
    (hw : ∀ x ∈ s, 0 ≤ w x) (k : ℕ) :
    (∑ t ∈ s.powersetCard k, ∏ x ∈ t, w x) ≤
      (s.card.choose k : ℝ) * ((∑ i ∈ s, w i) / (s.card : ℝ)) ^ k := by
  classical
  let a := (∑ i ∈ s, w i) / (s.card : ℝ)
  have ha : 0 ≤ a := div_nonneg (Finset.sum_nonneg hw) (Nat.cast_nonneg _)
  change _ ≤ (s.card.choose k : ℝ) * a ^ k
  induction k with
  | zero => simp
  | succ k ih =>
    by_cases hk : k < s.card
    · have hs : 0 < s.card := Nat.zero_le k |>.trans_lt hk
      have hc : (0 : ℝ) ≤ (s.card : ℝ) - k := sub_nonneg.mpr (by exact_mod_cast hk.le)
      apply (le_of_mul_le_mul_left (a := (k + 1 : ℝ))) _ (by positivity)
      calc
        _ ≤ ((s.card : ℝ) - k) * a * (∑ t ∈ s.powersetCard k, ∏ x ∈ t, w x) :=
          weighted_subsets_next_le s w hs hw k
        _ ≤ ((s.card : ℝ) - k) * a * ((s.card.choose k : ℝ) * a ^ k) :=
          mul_le_mul_of_nonneg_left ih (mul_nonneg hc ha)
        _ = _ := by
          have hchoose : (s.card.choose (k + 1) : ℝ) * (k + 1 : ℝ) =
              (s.card.choose k : ℝ) * ((s.card : ℝ) - k) := by
            have hh := congrArg (fun x : ℕ ↦ (x : ℝ)) (Nat.choose_succ_right_eq s.card k)
            simpa only [Nat.cast_mul, Nat.cast_succ, Nat.cast_sub hk.le] using hh
          rw [pow_succ, ← mul_assoc (k + 1 : ℝ), mul_comm (k + 1 : ℝ), hchoose]
          ring
    · have hk' : s.card < k + 1 := by omega
      rw [Finset.powersetCard_eq_empty.mpr hk', Finset.sum_empty]
      exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ha _)

end BoundedEdgeRegularSubgraphs
