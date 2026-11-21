module

public import CutSpectral
public import Mathlib.Combinatorics.SimpleGraph.Regularity.Lemma
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition

open Finset
open scoped Classical

variable {V : Type*}

private theorem rect_eq_density (G : SimpleGraph V) (p : ℝ) (X Y : Finset V) :
    (∑ x ∈ X, ∑ y ∈ Y, centered G p x y) =
      ((G.edgeDensity X Y : ℝ) - p)*((X.card : ℝ)*Y.card) := by
  classical
  have he : (∑ x ∈ X, ∑ y ∈ Y, if G.Adj x y then (1:ℝ) else 0) = (G.interedges X Y).card := by
    rw [← sum_product']
    simp [G.interedges_def]
  by_cases hX : X = ∅
  · simp [hX]
  by_cases hY : Y = ∅
  · simp [hY]
  have hx : (X.card : ℝ) ≠ 0 := by exact_mod_cast card_ne_zero.mpr (nonempty_iff_ne_empty.mpr hX)
  have hy : (Y.card : ℝ) ≠ 0 := by exact_mod_cast card_ne_zero.mpr (nonempty_iff_ne_empty.mpr hY)
  simp only [centered, sum_sub_distrib, sum_const, nsmul_eq_mul, he, G.edgeDensity_def,
    Rat.cast_div, Rat.cast_mul, Rat.cast_natCast]
  field_simp

private theorem density_error_le_one (G : SimpleGraph V) (X Y : Finset V) (p : ℝ)
    (hp : 0 ≤ p) (hp' : p ≤ 1) : |(G.edgeDensity X Y : ℝ) - p| ≤ 1 := by
  have h₁ : (0:ℝ) ≤ G.edgeDensity X Y := by exact_mod_cast G.edgeDensity_nonneg X Y
  have h₂ : (G.edgeDensity X Y : ℝ) ≤ 1 := by exact_mod_cast G.edgeDensity_le_one X Y
  exact abs_le.mpr ⟨by linarith,by linarith⟩

private theorem pair_discrepancy (G : SimpleGraph V) (A B X Y : Finset V) (p e : ℝ)
    (hp : 0 ≤ p) (hp' : p ≤ 1) (he : 0 ≤ e) (hXA : X ⊆ A) (hYB : Y ⊆ B)
    (uniform : G.IsUniform e A B) (close : |(G.edgeDensity A B : ℝ) - p| ≤ e) :
    |∑ x ∈ X, ∑ y ∈ Y, centered G p x y| ≤ (2*e)*((A.card : ℝ)*B.card) := by
  rw [rect_eq_density, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (X.card : ℝ)*Y.card)]
  have hX : (X.card : ℝ) ≤ A.card := by exact_mod_cast card_le_card hXA
  have hY : (Y.card : ℝ) ≤ B.card := by exact_mod_cast card_le_card hYB
  have prod := mul_le_mul hX hY (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have small := mul_le_mul_of_nonneg_right (density_error_le_one G X Y p hp hp')
    (show 0 ≤ (X.card : ℝ)*Y.card by positivity)
  rw [one_mul] at small
  by_cases ax : (A.card : ℝ)*e ≤ X.card
  · by_cases by' : (B.card : ℝ)*e ≤ Y.card
    · have bound := (abs_sub_le (G.edgeDensity X Y : ℝ) (G.edgeDensity A B) p).trans
        (add_le_add (uniform hXA hYB ax by').le close)
      rw [← two_mul] at bound
      exact mul_le_mul bound prod (by positivity) (by positivity)
    · have h := mul_le_mul hX (le_of_not_ge by') (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      exact small.trans (h.trans (by nlinarith [mul_nonneg he (show 0 ≤ (A.card : ℝ)*B.card by positivity)]))
  · have h := mul_le_mul (le_of_not_ge ax) hY (Nat.cast_nonneg _) (by positivity)
    exact small.trans (h.trans (by nlinarith [mul_nonneg he (show 0 ≤ (A.card : ℝ)*B.card by positivity)]))

/-- A union of pairwise regular parts with nearby densities has small discrepancy.
The final term is the cost of the diagonal pairs of parts. -/
theorem discrepancy_of_parts (G : SimpleGraph V) (P : Finset (Finset V))
    (disj : (P : Set (Finset V)).PairwiseDisjoint id)
    (p e m : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) (he : 0 ≤ e)
    (size : ∀ A ∈ P, (A.card : ℝ) ≤ m)
    (pairs : ∀ A ∈ P, ∀ B ∈ P, A ≠ B →
      G.IsUniform e A B ∧ |(G.edgeDensity A B : ℝ) - p| ≤ e) :
    let U := P.biUnion id
    CutDiscrepancy G U p (2*e*(U.card : ℝ)^2 + m*U.card) := by
  classical
  let U := P.biUnion id
  have cardU : (U.card : ℝ) = ∑ A ∈ P, (A.card : ℝ) := by exact_mod_cast card_biUnion disj
  have decomp (X : Finset V) (hX : X ⊆ U) (f : V → ℝ) :
      (∑ x ∈ X, f x) = ∑ A ∈ P, ∑ x ∈ X ∩ A, f x := by
    have cover : X = P.biUnion fun A => X ∩ A := by
      calc
        X = X ∩ U := (inter_eq_left.mpr hX).symm
        _ = _ := inter_biUnion X P id
    conv_lhs => rw [cover]
    exact sum_biUnion (fun a ha b hb hn => (disj ha hb hn).mono inter_subset_right inter_subset_right)
  change CutDiscrepancy G U p (2*e*(U.card : ℝ)^2 + m*U.card)
  intro X hX Y hY
  rw [decomp X hX]
  simp_rw [decomp Y hY]
  have exchange (A : Finset V) :
      (∑ x ∈ X ∩ A, ∑ B ∈ P, ∑ y ∈ Y ∩ B, centered G p x y) =
      ∑ B ∈ P, ∑ x ∈ X ∩ A, ∑ y ∈ Y ∩ B, centered G p x y := sum_comm
  simp_rw [exchange]
  let W := fun (A B : Finset V) => (2*e) * ((A.card : ℝ)*B.card) + (if A = B then m*(A.card : ℝ) else 0)
  have block (A) (hA : A ∈ P) (B) (hB : B ∈ P) :
      |∑ x ∈ X ∩ A, ∑ y ∈ Y ∩ B, centered G p x y| ≤ W A B := by
    by_cases h : A = B
    · subst B
      have hX' : ((X ∩ A).card : ℝ) ≤ m := (Nat.cast_le.mpr (card_le_card inter_subset_right)).trans (size A hA)
      have hY' : ((Y ∩ A).card : ℝ) ≤ A.card := Nat.cast_le.mpr (card_le_card inter_subset_right)
      rw [rect_eq_density, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ((X ∩ A).card : ℝ)*(Y ∩ A).card)]
      have hb := mul_le_mul (density_error_le_one G (X ∩ A) (Y ∩ A) p hp hp')
        (mul_le_mul hX' hY' (by positivity) ((Nat.cast_nonneg _).trans (size A hA))) (by positivity) zero_le_one
      simp only [W, one_mul] at *
      exact hb.trans (le_add_of_nonneg_left (by positivity))
    · simpa [W,h] using pair_discrepancy G A B (X ∩ A) (Y ∩ B) p e hp hp' he inter_subset_right
        inter_subset_right (pairs A hA B hB h).1 (pairs A hA B hB h).2
  calc
    _ ≤ ∑ A ∈ P, |∑ B ∈ P, ∑ x ∈ X ∩ A, ∑ y ∈ Y ∩ B, centered G p x y| := abs_sum_le_sum_abs ..
    _ ≤ ∑ A ∈ P, ∑ B ∈ P, W A B := sum_le_sum fun A hA =>
      (abs_sum_le_sum_abs ..).trans (sum_le_sum fun B hB => block A hA B hB)
    _ = _ := by
      rw [cardU]
      simp only [W, sum_add_distrib, ← mul_assoc, ← mul_sum, ← sum_mul,
        sum_ite_eq]
      simp [← mul_sum, mul_assoc, pow_two]

end InducedDegreeRepetition
