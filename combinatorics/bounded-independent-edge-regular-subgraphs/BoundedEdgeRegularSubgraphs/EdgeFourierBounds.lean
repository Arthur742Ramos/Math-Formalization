module

public import BoundedEdgeRegularSubgraphs.ScalarAtoms
import BoundedEdgeRegularSubgraphs.BernoulliFourier
import Mathlib.Tactic

/-!
# Modulus bound on the degree Fourier integrand

A positive proportion of edges with large half-angle sine forces
exponential decay in the number of those edges.
-/

public section

open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]

omit [Fintype α] in
private theorem edgeCharacter_coe (e : Edge α) (t : α → ℝ) :
    edgeCharacter e (fun i ↦ (t i : PhaseCircle)) =
      Complex.exp (((t e.val.1 + t e.val.2 : ℝ) : ℂ) * Complex.I) := by
  unfold edgeCharacter
  rw [fourier_one_coe, fourier_one_coe, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The exponential bound in terms of the sum of squared half-angle sines. -/
theorem degreeFourier_norm_le_sine_sum (A : Finset (Edge α))
    (p : Edge α → Set.Icc (0 : ℝ) 1) (d : α → ℤ) (t : α → ℝ) (ξ : ℝ)
    (hp : ∀ e ∈ A, ξ ≤ (p e : ℝ) ∧ (p e : ℝ) ≤ 1 - ξ) :
    ‖degreeFourier A p d (fun i ↦ (t i : PhaseCircle))‖ ≤
      Real.exp (-(2 * ξ * (1 - ξ)) *
        ∑ e ∈ A, Real.sin ((t e.val.1 + t e.val.2) / 2) ^ 2) := by
  let s (e : Edge α) := t e.val.1 + t e.val.2
  have hχ : ∀ y : α → PhaseCircle, ‖latticeCharacter (-d) y‖ = 1 := by
    intro y
    simp [latticeCharacter, norm_prod]
  have hvar (e : Edge α) (he : e ∈ A) : ξ * (1 - ξ) ≤ (p e : ℝ) * (1 - p e) := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr (hp e he).1) (sub_nonneg.mpr (hp e he).2)]
  unfold degreeFourier
  rw [norm_mul, hχ, one_mul, Complex.norm_prod]
  calc
    _ = ∏ e ∈ A, ‖bernoulliFourierFactor (p e) (s e)‖ := by
      apply Finset.prod_congr rfl
      intro e _
      rw [edgeCharacter_coe]
      rfl
    _ ≤ ∏ e ∈ A, Real.exp (-(2 * ξ * (1 - ξ)) * Real.sin (s e / 2) ^ 2) := by
      refine Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun e he ↦
        (bernoulliFourierFactor_norm_le _ _).trans (Real.exp_le_exp.mpr ?_))
      nlinarith only [mul_le_mul_of_nonneg_right (hvar e he) (sq_nonneg (Real.sin (s e / 2)))]
    _ = _ := by rw [← Real.exp_sum, Finset.mul_sum]

/-- Many bad edges give the pointwise exponential estimate in the first part of Lemma B.1. -/
theorem degreeFourier_norm_le_bad_count (A : Finset (Edge α))
    (p : Edge α → Set.Icc (0 : ℝ) 1) (d : α → ℤ) (t : α → ℝ)
    (ξ r : ℝ) (hξ : 0 ≤ ξ) (hξ' : ξ ≤ 1)
    (hp : ∀ e ∈ A, ξ ≤ (p e : ℝ) ∧ (p e : ℝ) ≤ 1 - ξ) :
    ‖degreeFourier A p d (fun i ↦ (t i : PhaseCircle))‖ ≤
      Real.exp (-(2 * ξ * (1 - ξ)) * r *
        ((A.filter fun e ↦ r ≤ Real.sin ((t e.val.1 + t e.val.2) / 2) ^ 2).card : ℝ)) := by
  classical
  let f (e : Edge α) := Real.sin ((t e.val.1 + t e.val.2) / 2) ^ 2
  let B := A.filter (fun e ↦ r ≤ f e)
  have hs : r * (B.card : ℝ) ≤ ∑ e ∈ A, f e := by
    calc
      _ = ∑ _ ∈ B, r := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ e ∈ B, f e := Finset.sum_le_sum (fun e he ↦ (Finset.mem_filter.mp he).2)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ ↦ sq_nonneg _)
  refine (degreeFourier_norm_le_sine_sum A p d t ξ hp).trans (Real.exp_le_exp.mpr ?_)
  have hmul : 0 ≤ 2 * ξ * (1 - ξ) := mul_nonneg (mul_nonneg (by norm_num) hξ) (sub_nonneg.mpr hξ')
  have hb := mul_le_mul_of_nonneg_left hs hmul
  change -(2 * ξ * (1 - ξ)) * (∑ e ∈ A, f e) ≤ -(2 * ξ * (1 - ξ)) * r * (B.card : ℝ)
  linarith only [hb]

end BoundedEdgeRegularSubgraphs
