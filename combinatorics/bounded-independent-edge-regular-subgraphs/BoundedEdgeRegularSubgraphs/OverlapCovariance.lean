module

public import BoundedEdgeRegularSubgraphs.Covariance
import BoundedEdgeRegularSubgraphs.Induce
import BoundedEdgeRegularSubgraphs.MeanDrift
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

/-!
# Spectral bounds after deleting the overlap clique
-/

public section

open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]

theorem sum_edges_inside (S : Finset α) (v : α → ℝ) :
    (∑ e ∈ (Finset.univ.filter fun e : Edge α ↦ e.val.1 ∈ S ∧ e.val.2 ∈ S),
      (v e.val.1 + v e.val.2) ^ 2) =
      (S.card - 2 : ℝ) * (∑ i ∈ S, (v i) ^ 2) + (∑ i ∈ S, v i) ^ 2 := by
  classical
  have heq : (∑ e : Edge ↥S, (v e.val.1.val + v e.val.2.val) ^ 2) =
      ∑ e ∈ (Finset.univ.filter fun e : Edge α ↦ e.val.1 ∈ S ∧ e.val.2 ∈ S),
        (v e.val.1 + v e.val.2) ^ 2 := by
    refine Finset.sum_bij (fun e _ ↦ inducedEdge S e) ?_ ?_ ?_ ?_
    · intro e _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.val.1.property, e.val.2.property⟩
    · intro e _ f _ h
      exact inducedEdge_injective S h
    · intro e he
      obtain ⟨h₁, h₂⟩ := (Finset.mem_filter.mp he).2
      refine ⟨⟨(⟨e.val.1, h₁⟩, ⟨e.val.2, h₂⟩), e.property⟩, Finset.mem_univ _, ?_⟩
      exact Subtype.ext rfl
    · intros
      rfl
  rw [← heq]
  rw [← (Finset.sum_coe_sort S (fun i : α ↦ (v i) ^ 2)), ← (Finset.sum_coe_sort S v)]
  simpa only [Fintype.card_coe] using
    (sum_edge_squares (fun i : ↥S ↦ v i))

private theorem sum_edges_outside_overlap_identity (S : Finset α) (v : α → ℝ) :
    (∑ e ∈ edgesOutsideOverlap S, (v e.val.1 + v e.val.2) ^ 2) =
      (Fintype.card α - 2 : ℝ) * (∑ i, v i ^ 2) + (∑ i, v i) ^ 2 -
        ((S.card - 2 : ℝ) * (∑ i ∈ S, (v i) ^ 2) + (∑ i ∈ S, v i) ^ 2) := by
  classical
  rw [← sum_edge_squares, ← sum_edges_inside]
  apply eq_sub_of_add_eq
  rw [add_comm]
  exact Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun e : Edge α ↦ e.val.1 ∈ S ∧ e.val.2 ∈ S) (fun e ↦ (v e.val.1 + v e.val.2) ^ 2)

private theorem energy_deletion_lower (S : Finset α)
    (hm : 3 ≤ ((Finset.univ : Finset α) \ S).card) (v : α → ℝ) :
    ((((Finset.univ : Finset α) \ S).card : ℝ) ^ 2 / (3 * Fintype.card α)) *
        (∑ i, v i ^ 2) ≤ ∑ e ∈ edgesOutsideOverlap S, (v e.val.1 + v e.val.2) ^ 2 := by
  classical
  let O := (Finset.univ : Finset α) \ S
  let m : ℝ := O.card
  let n : ℝ := Fintype.card α
  let j : ℝ := S.card
  let a : ℝ := ∑ i ∈ S, v i ^ 2
  let b : ℝ := ∑ i ∈ O, v i ^ 2
  let u : ℝ := ∑ i ∈ S, v i
  let w : ℝ := ∑ i ∈ O, v i
  have hcount : m + j = n := by
    have hc := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
    rw [Finset.card_univ] at hc
    dsimp [m, j, n, O]
    exact_mod_cast hc
  have hm3 : (3 : ℝ) ≤ m := by
    dsimp [m, O]
    exact_mod_cast hm
  have hj0 : 0 ≤ j := Nat.cast_nonneg _
  have hm0 : 0 < m := by linarith
  have hn0 : 0 < n := by linarith
  have hmn : m ≤ n := by linarith
  have ha : 0 ≤ a := Finset.sum_nonneg (fun i _ ↦ sq_nonneg (v i))
  have hb : 0 ≤ b := Finset.sum_nonneg (fun i _ ↦ sq_nonneg (v i))
  have hsquares : ∑ i, v i ^ 2 = b + a := (Finset.sum_sdiff (Finset.subset_univ S)).symm
  have hsum : ∑ i, v i = w + u := (Finset.sum_sdiff (Finset.subset_univ S)).symm
  have hu : u ^ 2 ≤ j * a := sq_sum_le_card_mul_sum_sq
  have hw : w ^ 2 ≤ m * b := sq_sum_le_card_mul_sum_sq
  have hcross : -(m / n) * u ^ 2 - (n / m) * w ^ 2 ≤ 2 * u * w := by
    apply (le_of_mul_le_mul_right (a := m * n)) ?_ (mul_pos hm0 hn0)
    field_simp [hm0.ne', hn0.ne']
    nlinarith only [sq_nonneg (m * u + n * w)]
  have h1 := mul_le_mul_of_nonneg_left hu (div_nonneg hm0.le hn0.le)
  have h2 := mul_le_mul_of_nonneg_left hw (div_nonneg hj0 hm0.le)
  have hcoef : n / m - 1 = j / m := by
    field_simp [hm0.ne']
    linarith
  have h2' : (n / m - 1) * w ^ 2 ≤ j * b := by
    rw [hcoef]
    calc
      _ ≤ (j / m) * (m * b) := h2
      _ = _ := by field_simp [hm0.ne']
  have he1 : m ^ 2 / n * a ≤ m * a - (m / n) * (j * a) := by
    have hj' : j = n - m := by linarith
    rw [hj']
    apply Eq.le
    field_simp [hn0.ne']
    ring
  have he2 : m ^ 2 / (3 * n) ≤ m - 2 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hn0)).mpr
    have hmul := mul_le_mul_of_nonneg_left hmn hm0.le
    have hmul' := mul_le_mul_of_nonneg_left (show m ≤ 3 * (m - 2) by linarith) hn0.le
    nlinarith only [hmul, hmul']
  have he3 : m ^ 2 / (3 * n) ≤ m ^ 2 / n := by
    rw [mul_comm (3 : ℝ) n, ← div_div]
    linarith [div_nonneg (sq_nonneg m) hn0.le]
  rw [sum_edges_outside_overlap_identity, hsquares, hsum]
  change m ^ 2 / (3 * n) * (b + a) ≤ (n - 2) * (b + a) + (w + u) ^ 2 -
    ((j - 2) * a + u ^ 2)
  have hin := mul_le_mul_of_nonneg_right he3 ha
  have hout := mul_le_mul_of_nonneg_right he2 hb
  have hcombine := congrArg (fun x : ℝ ↦ x * b + x * a) hcount
  linarith only [hcross, h1, h2', he1, hin, hout, hcombine]

/-- Explicit spectral bounds when only edges with both endpoints in the overlap are deleted. -/
theorem degreeCovariance_outside_overlap_bounds (S : Finset α)
    (hm : 3 ≤ ((Finset.univ : Finset α) \ S).card)
    (p : Edge α → Set.Icc (0 : ℝ) 1) (lower : ℝ) (hlower : 0 ≤ lower)
    (hp : ∀ e, lower ≤ (p e : ℝ) * (1 - p e)) (v : α → ℝ) :
    lower * ((((Finset.univ : Finset α) \ S).card : ℝ) ^ 2 / (3 * Fintype.card α)) *
      (∑ i, v i ^ 2) ≤
      (∑ i, ∑ j, v i * degreeCovariance (edgesOutsideOverlap S) p i j * v j) ∧
    (∑ i, ∑ j, v i * degreeCovariance (edgesOutsideOverlap S) p i j * v j) ≤
      (Fintype.card α - 1 : ℝ) / 2 * ∑ i, v i ^ 2 := by
  rw [degreeCovariance_quadratic]
  constructor
  · rw [mul_assoc]
    calc
      _ ≤ lower * ∑ e ∈ edgesOutsideOverlap S, (v e.val.1 + v e.val.2) ^ 2 :=
        mul_le_mul_of_nonneg_left (energy_deletion_lower S hm v) hlower
      _ ≤ _ := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum (fun e _ ↦ mul_le_mul_of_nonneg_right (hp e) (sq_nonneg _))
  · have h := (degreeCovariance_univ_bounds p lower hlower hp v).2
    rw [degreeCovariance_quadratic] at h
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_) h
    intro e _ _
    exact mul_nonneg (mul_nonneg (p e).property.1 (sub_nonneg.mpr (p e).property.2)) (sq_nonneg _)

end BoundedEdgeRegularSubgraphs
