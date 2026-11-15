/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Gram.SOS
public import Mathlib.Data.Fintype.Fin

/-!
# Integer checking of Gram residual certificates

The certificate consists of an integer matrix, an integer proposed factor,
and two positive scale factors.  Only exact integer equalities and inequalities
enter the proof.  The external procedure proposing the factor is untrusted.
-/

@[expose] public section

namespace ErdosOverlap.Gram

open scoped BigOperators

/-- Total access for a literal integer table. Dimensions are enforced by the
finite indices of the matrix being certified. Missing entries mean zero. -/
def tableMatrix {n : ℕ} (a : Array (Array ℤ)) (i j : Fin n) : ℤ :=
  (a.getD i.val #[]).getD j.val 0

def intGram {ι κ : Type*} [Fintype κ] (B : ι → κ → ℤ) (i j : ι) : ℤ :=
  ∑ k, B i k * B j k

def intResidual {ι κ : Type*} [Fintype κ]
    (A : ι → ι → ℤ) (B : ι → κ → ℤ) (s c : ℤ) (i j : ι) : ℤ :=
  c ^ 2 * A i j - s * intGram B i j

def IntDiagonallyDominant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → ℤ) : Prop :=
  ∀ i, (∑ j, if i = j then 0 else |A i j|) ≤ A i i

instance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → ℤ) : Decidable (IntDiagonallyDominant A) :=
  inferInstanceAs (Decidable (∀ i, (∑ j, if i = j then 0 else |A i j|) ≤ A i i))

theorem intResidual_symm {ι κ : Type*} [Fintype κ]
    (A : ι → ι → ℤ) (B : ι → κ → ℤ) (s c : ℤ)
    (hsym : ∀ i j, A i j = A j i) :
    ∀ i j, intResidual A B s c i j = intResidual A B s c j i := by
  intro i j
  simp only [intResidual, intGram, hsym i j]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  exact mul_comm _ _

theorem form_nonneg_of_int_dominant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : ι → ι → ℤ) (hsym : ∀ i j, R i j = R j i)
    (hdd : IntDiagonallyDominant R) (x : ι → ℝ) :
    0 ≤ form (fun i j => (R i j : ℝ)) x := by
  apply form_nonneg_of_diagonal_dominant
  · intro i j
    exact congrArg Int.cast (hsym i j)
  · intro i
    exact_mod_cast hdd i

/-- The integer residual criterion establishes PSD of the original integer
matrix, interpreted over the reals. -/
theorem form_nonneg_of_int_residual {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι]
    (A : ι → ι → ℤ) (B : ι → κ → ℤ) (s c : ℤ)
    (hs : 0 ≤ s) (hc : 0 < c)
    (hsym : ∀ i j, A i j = A j i)
    (hdd : IntDiagonallyDominant (intResidual A B s c))
    (x : ι → ℝ) : 0 ≤ form (fun i j => (A i j : ℝ)) x := by
  let R := intResidual A B s c
  have hR := form_nonneg_of_int_dominant R (intResidual_symm A B s c hsym) hdd x
  have hG := form_gram_nonneg (fun i k => (B i k : ℝ)) x
  have hs' : (0 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hc' : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hid : (fun i j => (c : ℝ) ^ 2 * (A i j : ℝ)) =
      (fun i j => (s : ℝ) * (∑ k, (B i k : ℝ) * (B j k : ℝ)) + (R i j : ℝ)) := by
    funext i j
    simp only [R, intResidual, intGram, Int.cast_sub, Int.cast_mul,
      Int.cast_pow, Int.cast_sum]
    ring
  have heq : (c : ℝ) ^ 2 * form (fun i j => (A i j : ℝ)) x =
      (s : ℝ) * form (fun i j => ∑ k, (B i k : ℝ) * (B j k : ℝ)) x +
      form (fun i j => (R i j : ℝ)) x := by
    rw [← form_scale, hid, form_add, form_scale]
  have hn : 0 ≤ (c : ℝ) ^ 2 * form (fun i j => (A i j : ℝ)) x := by
    rw [heq]
    exact add_nonneg (mul_nonneg hs' hG) hR
  exact (mul_nonneg_iff_of_pos_left (sq_pos_of_pos hc')).mp hn

/-- Dividing the certified integer matrix by any positive scale preserves
nonnegativity. This is the API for the rational phase Gram matrix. -/
theorem form_nonneg_of_int_residual_div {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι]
    (A : ι → ι → ℤ) (B : ι → κ → ℤ) (s c : ℤ)
    (hs : 0 < s) (hc : 0 < c)
    (hsym : ∀ i j, A i j = A j i)
    (hdd : IntDiagonallyDominant (intResidual A B s c))
    (x : ι → ℝ) : 0 ≤ form (fun i j => (A i j : ℝ) / (s : ℝ)) x := by
  have hn := form_nonneg_of_int_residual A B s c hs.le hc hsym hdd x
  have hs' : (0 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs.le
  have heq : (fun i j => (A i j : ℝ) / (s : ℝ)) =
      (fun i j => (s : ℝ)⁻¹ * (A i j : ℝ)) := by
    funext i j
    exact div_eq_inv_mul _ _
  rw [heq, form_scale]
  exact mul_nonneg (inv_nonneg.mpr hs') hn

end ErdosOverlap.Gram
