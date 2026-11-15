/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Gram.SOS
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Restriction of a quadratic form to the zero-sum subspace

The phase certificates eliminate the last cell coordinate.  This module
checks the corresponding algebra over the reals, independently of any
particular numerical certificate.
-/

@[expose] public section

namespace ErdosOverlap.Gram

open scoped BigOperators

noncomputable def restricted {n : ℕ}
    (G : Fin (n + 1) → Fin (n + 1) → ℝ) (i j : Fin n) : ℝ :=
  G i.castSucc j.castSucc - G i.castSucc (Fin.last n) -
    G (Fin.last n) j.castSucc + G (Fin.last n) (Fin.last n)

/-- Eliminating the final coordinate gives exactly the double-difference
matrix used by the rational phase certificate. -/
theorem form_eq_restricted_of_sum_zero {n : ℕ}
    (G : Fin (n + 1) → Fin (n + 1) → ℝ)
    (y : Fin (n + 1) → ℝ) (hy : ∑ i, y i = 0) :
    form G y = form (restricted G) (fun i => y i.castSucc) := by
  have hlast : y (Fin.last n) = -(∑ i : Fin n, y i.castSucc) := by
    rw [Fin.sum_univ_castSucc] at hy
    linarith
  unfold form restricted
  rw [Fin.sum_univ_castSucc]
  simp_rw [Fin.sum_univ_castSucc]
  rw [hlast]
  simp only [sub_mul, add_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    neg_mul, mul_neg, neg_neg, Finset.sum_neg_distrib]
  simp only [Finset.mul_sum, Finset.sum_mul]
  have h3 : (∑ i : Fin n, ∑ j : Fin n,
      G (Fin.last n) i.castSucc * y j.castSucc * y i.castSucc) =
      ∑ i : Fin n, ∑ j : Fin n,
        G (Fin.last n) j.castSucc * y i.castSucc * y j.castSucc :=
    Finset.sum_comm
  have h4 : (∑ i : Fin n, ∑ j : Fin n,
      G (Fin.last n) (Fin.last n) * y j.castSucc * y i.castSucc) =
      ∑ i : Fin n, ∑ j : Fin n,
        G (Fin.last n) (Fin.last n) * y i.castSucc * y j.castSucc := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [h3, h4]
  ring

/-- A PSD restricted matrix supplies the required quadratic-form premise on
every zero-sum phase cell vector. -/
theorem form_nonneg_on_sum_zero {n : ℕ}
    (G : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hG : ∀ x : Fin n → ℝ, 0 ≤ form (restricted G) x)
    (y : Fin (n + 1) → ℝ) (hy : ∑ i, y i = 0) :
    0 ≤ form G y := by
  rw [form_eq_restricted_of_sum_zero G y hy]
  exact hG _

end ErdosOverlap.Gram
