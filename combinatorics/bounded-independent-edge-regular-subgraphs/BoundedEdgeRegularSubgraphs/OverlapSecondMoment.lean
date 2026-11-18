module

public import BoundedEdgeRegularSubgraphs.WeightedSecondMoment
public import BoundedEdgeRegularSubgraphs.IntersectionProbability
import Mathlib.Tactic

/-!
# Organizing the weighted second moment by intersection size
-/

public section

open MeasureTheory
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α Ω : Type*} [DecidableEq α] [MeasurableSpace Ω]

/-- The variance estimate in §3. Overlaps of size at most one cancel
exactly. Larger overlaps are bounded using (3.2). -/
theorem probability_no_candidate_le_overlap_sum (μ : Measure Ω)
    [IsProbabilityMeasure μ] (s : Finset α) (k : ℕ) (F : Finset (Finset α))
    (hF : F ⊆ s.powersetCard k) (hF₀ : F.Nonempty)
    (hhalf : s.card.choose k ≤ 2 * F.card)
    (E : Finset α → Set Ω) (hE : ∀ S ∈ F, MeasurableSet (E S))
    (hp : ∀ S ∈ F, 0 < μ.real (E S)) (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j)
    (hind : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).card ≤ 1 →
      μ.real (E S ∩ E T) = μ.real (E S) * μ.real (E T))
    (hjoint : ∀ S ∈ F, ∀ T ∈ F, 2 ≤ (S ∩ T).card →
      μ.real (E S ∩ E T) / (μ.real (E S) * μ.real (E T)) ≤ b (S ∩ T).card) :
    let m := (k : ℝ) ^ 2 / s.card
    μ.real (⋂ S ∈ F, (E S)ᶜ) ≤
      4 * ∑ j ∈ Finset.Icc 2 k, min (m ^ j) ((Real.exp 1 * m / j) ^ j) * b j := by
  classical
  intro m
  let L := Finset.Icc 2 k
  let q (j : ℕ) := min (m ^ j) ((Real.exp 1 * m / j) ^ j)
  let N : ℝ := s.card.choose k
  let f : ℝ := F.card
  let r (S T : Finset α) := μ.real (E S ∩ E T) / (μ.real (E S) * μ.real (E T))
  have hq (j : ℕ) : 0 ≤ q j := by
    dsimp only [q]
    have hm : 0 ≤ m := by dsimp only [m]; positivity
    exact le_min (pow_nonneg hm _) (pow_nonneg (by positivity) _)
  have hf : 0 < f := Nat.cast_pos.mpr hF₀.card_pos
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hhalf' : N ≤ 2 * f := by dsimp only [N, f]; exact_mod_cast hhalf
  have hpoint {S T : Finset α} (hS : S ∈ F) (hT : T ∈ F) :
      r S T - 1 ≤ ∑ j ∈ L, if (S ∩ T).card = j then b j else 0 := by
    rcases le_or_gt (S ∩ T).card 1 with h | h
    · have hh : r S T = 1 := by
        dsimp only [r]
        rw [hind S hS T hT h, div_self (mul_pos (hp S hS) (hp T hT)).ne']
      rw [hh, sub_self]
      exact Finset.sum_nonneg (fun j _ ↦ by split_ifs; exacts [hb _, le_rfl])
    · have hcard := (Finset.mem_powersetCard.mp (hF hS)).2
      have hi : (S ∩ T).card ∈ L := Finset.mem_Icc.mpr ⟨by omega,
        (Finset.card_le_card Finset.inter_subset_left).trans hcard.le⟩
      rw [Finset.sum_eq_single_of_mem _ hi (fun j _ hj ↦ ite_eq_right (Ne.symm hj)), ite_eq_left rfl]
      exact (sub_le_self _ zero_le_one).trans (hjoint S hS T hT (by omega))
  have hsum (S : Finset α) (hS : S ∈ F) :
      (∑ T ∈ F, (r S T - 1)) ≤ N * ∑ j ∈ L, q j * b j := by
    obtain ⟨hSs, hSk⟩ := Finset.mem_powersetCard.mp (hF hS)
    calc
      _ ≤ ∑ T ∈ F, ∑ j ∈ L, if (S ∩ T).card = j then b j else 0 :=
        Finset.sum_le_sum (fun T hT ↦ hpoint hS hT)
      _ = ∑ j ∈ L, ((F.filter fun T ↦ (S ∩ T).card = j).card : ℝ) * b j := by
        rw [Finset.sum_comm]
        simp_rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ j ∈ L, (N * q j) * b j := by
        apply Finset.sum_le_sum
        intro j hj
        have hjs := Finset.mem_Icc.mp hj
        apply mul_le_mul_of_nonneg_right _ (hb j)
        have hsub : (F.filter fun T ↦ (S ∩ T).card = j) ⊆
            (s.powersetCard k).filter (fun T ↦ (S ∩ T).card = j) :=
          Finset.filter_subset_filter _ hF
        exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
          (card_sample_intersection_eq_le s S hSs hSk (by omega) hjs.2)
      _ = _ := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ ↦ mul_assoc _ _ _)
  have hdiff : (∑ S ∈ F, ∑ T ∈ F, r S T) - f ^ 2 =
      ∑ S ∈ F, ∑ T ∈ F, (r S T - 1) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, f, pow_two]
  have hext : (∑ S ∈ F, ∑ T ∈ F, r S T) - f ^ 2 ≤
      f * N * ∑ j ∈ L, q j * b j := by
    rw [hdiff]
    calc
      _ ≤ ∑ _ ∈ F, (N * ∑ j ∈ L, q j * b j) := Finset.sum_le_sum hsum
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]
  have hnonneg : 0 ≤ ∑ j ∈ L, q j * b j :=
    Finset.sum_nonneg (fun j _ ↦ mul_nonneg (hq j) (hb j))
  have hs := probability_no_event_le_weighted_second_moment μ F hF₀ E hE hp
  change _ ≤ ((∑ S ∈ F, ∑ T ∈ F, r S T) - f ^ 2) / f ^ 2 at hs
  refine hs.trans ((div_le_div_of_nonneg_right hext (by positivity)).trans ?_)
  apply (div_le_iff₀ (sq_pos_of_pos hf)).2
  have hhh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhalf' hf.le) hnonneg
  have hbound : f * N * (∑ j ∈ L, q j * b j) ≤ 4 * (∑ j ∈ L, q j * b j) * f ^ 2 := by
    nlinarith only [hhh, mul_nonneg (sq_nonneg f) hnonneg]
  exact hbound

end BoundedEdgeRegularSubgraphs
