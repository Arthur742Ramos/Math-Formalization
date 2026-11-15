/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Quadratic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Exact sum-of-squares certificates for symmetric matrices

A rounded factorization is useful only as a proposed witness.  This module
proves that an exact decomposition into a Gram matrix and a symmetric,
diagonally dominant residual implies nonnegativity of the quadratic form.
The criterion uses no eigenvalue computation or unverified numerical result.
-/

@[expose] public section

namespace ErdosOverlap.Gram

open scoped BigOperators

noncomputable def form {ι : Type*} [Fintype ι]
    (A : ι → ι → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * x i * x j

theorem form_add {ι : Type*} [Fintype ι]
    (A B : ι → ι → ℝ) (x : ι → ℝ) :
    form (fun i j => A i j + B i j) x = form A x + form B x := by
  simp only [form, add_mul, Finset.sum_add_distrib]

theorem form_scale {ι : Type*} [Fintype ι]
    (c : ℝ) (A : ι → ι → ℝ) (x : ι → ℝ) :
    form (fun i j => c * A i j) x = c * form A x := by
  simp only [form, mul_assoc, Finset.mul_sum]

theorem form_gram {ι κ : Type*} [Fintype ι] [Fintype κ]
    (B : ι → κ → ℝ) (x : ι → ℝ) :
    form (fun i j => ∑ k, B i k * B j k) x =
      ∑ k, (∑ i, B i k * x i) ^ 2 := by
  unfold form
  simp only [Finset.sum_mul]
  calc
    (∑ i, ∑ j, ∑ k, B i k * B j k * x i * x j) =
        ∑ i, ∑ k, ∑ j, B i k * B j k * x i * x j := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, B i k * B j k * x i * x j :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

theorem form_gram_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ]
    (B : ι → κ → ℝ) (x : ι → ℝ) :
    0 ≤ form (fun i j => ∑ k, B i k * B j k) x := by
  rw [form_gram]
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

private theorem pair_nonneg (r x y : ℝ) :
    0 ≤ |r| * x ^ 2 + |r| * y ^ 2 + 2 * (r * x * y) := by
  by_cases hr : 0 ≤ r
  · rw [abs_of_nonneg hr]
    nlinarith [mul_nonneg hr (sq_nonneg (x + y))]
  · rw [abs_of_neg (lt_of_not_ge hr)]
    nlinarith [mul_nonneg (le_of_lt (neg_pos.mpr (lt_of_not_ge hr)))
      (sq_nonneg (x - y))]

/-- A symmetric off-diagonal matrix is bounded below by the negative of its
absolute row sums, evaluated against the coordinate squares. -/
theorem form_ge_neg_row_abs {ι : Type*} [Fintype ι]
    (A : ι → ι → ℝ) (hsym : ∀ i j, A i j = A j i) (x : ι → ℝ) :
    -(∑ i, (∑ j, |A i j|) * x i ^ 2) ≤ form A x := by
  have hp := Finset.sum_nonneg (s := (Finset.univ : Finset ι))
    (fun i _ => Finset.sum_nonneg (s := (Finset.univ : Finset ι))
      (fun j _ => pair_nonneg (A i j) (x i) (x j)))
  have hswap : (∑ i, ∑ j, |A i j| * x j ^ 2) =
      ∑ i, ∑ j, |A i j| * x i ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsym j i]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hp
  rw [hswap] at hp
  simp only [← Finset.sum_mul] at hp
  unfold form
  linarith

/-- Symmetric row diagonal dominance with nonnegative diagonal implies
nonnegativity of the quadratic form. -/
theorem form_nonneg_of_diagonal_dominant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → ℝ) (hsym : ∀ i j, A i j = A j i)
    (hdd : ∀ i, (∑ j, if i = j then 0 else |A i j|) ≤ A i i)
    (x : ι → ℝ) : 0 ≤ form A x := by
  let O : ι → ι → ℝ := fun i j => if i = j then 0 else A i j
  have ho : ∀ i j, O i j = O j i := by
    intro i j
    by_cases h : i = j
    · subst j
      simp [O]
    · simp only [O, h, Ne.symm h, ↓reduceIte]
      exact hsym i j
  have hb := form_ge_neg_row_abs O ho x
  have hd : (∑ i, (∑ j, |O i j|) * x i ^ 2) ≤
      ∑ i, A i i * x i ^ 2 := by
    apply Finset.sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    simpa only [O, apply_ite abs, abs_zero] using hdd i
  have heq : form A x = (∑ i, A i i * x i ^ 2) + form O x := by
    let D : ι → ι → ℝ := fun i j => if i = j then A i i else 0
    have ha : A = fun i j => D i j + O i j := by
      funext i j
      by_cases h : i = j
      · subst j
        simp [D, O]
      · simp [D, O, h]
    have hdiag : form D x = ∑ i, A i i * x i ^ 2 := by
      simp [form, D, pow_two, mul_assoc]
    calc
      form A x = form (fun i j => D i j + O i j) x :=
        congrArg (fun Z => form Z x) ha
      _ = _ := by rw [form_add, hdiag]
  linarith

/-- An exact Gram-plus-diagonally-dominant decomposition is a sound PSD
certificate.  The factors may have been discovered by any external method. -/
theorem form_nonneg_of_sos_residual {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι]
    (A R : ι → ι → ℝ) (B : ι → κ → ℝ) (s : ℝ)
    (hs : 0 ≤ s)
    (hid : ∀ i j, A i j = (∑ k, B i k * B j k) + s * R i j)
    (hsym : ∀ i j, R i j = R j i)
    (hdd : ∀ i, (∑ j, if i = j then 0 else |R i j|) ≤ R i i)
    (x : ι → ℝ) : 0 ≤ form A x := by
  have heq : A = fun i j => (∑ k, B i k * B j k) + s * R i j := by
    funext i j
    exact hid i j
  rw [heq, form_add, form_scale]
  exact add_nonneg (form_gram_nonneg B x)
    (mul_nonneg hs (form_nonneg_of_diagonal_dominant R hsym hdd x))

end ErdosOverlap.Gram
