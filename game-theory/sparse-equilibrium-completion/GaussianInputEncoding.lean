/- AI-assisted original-input and transient-value continuation; Apache-2.0.
Exact compilation/audit status is recorded in source-bound receipts.
The uncompiled original draft remains in source-input-bits-v1.
These are value/encoding bounds, not primitive or total running-time claims.
-/
module
public import GaussianCramerOutput
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
@[expose] public section
open scoped BigOperators
namespace SparseCompletion.Gaussian

def inputDenominatorProduct {r n : ℕ} (A : Matrix (Fin r) (Fin n) ℚ) : ℕ :=
  ∏ p : Fin r × Fin n, (A p.1 p.2).den

theorem inputDenominatorProduct_pos {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) ℚ) : 0 < inputDenominatorProduct A := by
  apply Finset.prod_pos
  intro p _
  exact (A p.1 p.2).den_pos

/-- The LCM used by the ACTUAL Mathlib numerator matrix divides the product
of original denominators, including an empty matrix's product one. -/
theorem matrix_den_dvd_input_product {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) ℚ) : A.den ∣ inputDenominatorProduct A := by
  apply Matrix.den_dvd_iff.mpr
  intro i j
  exact Finset.dvd_prod_of_mem (fun p : Fin r × Fin n => (A p.1 p.2).den)
    (Finset.mem_univ (i, j))

theorem matrix_den_le_input_product {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) ℚ) : A.den ≤ inputDenominatorProduct A := by
  exact Nat.le_of_dvd (inputDenominatorProduct_pos A) (matrix_den_dvd_input_product A)

theorem inputDenominatorProduct_le {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) ℚ) (D : ℕ)
    (hD : ∀ i j, (A i j).den ≤ D) : inputDenominatorProduct A ≤ D^(r*n) := by
  have hp := Finset.prod_le_prod (s := Finset.univ)
    (f := fun p : Fin r × Fin n => (A p.1 p.2).den)
    (g := fun _ => D) (fun p _ => hD p.1 p.2)
  simpa only [inputDenominatorProduct, Finset.prod_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin] using hp

/-- Exact normalization identity, with the LCM quotient derived from original
entry divisibility. The integer matrix is Mathlib's actual Matrix.num. -/
theorem matrix_num_eq_den_quotient_mul {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) ℚ) (i : Fin r) (j : Fin n) :
    ∃ t : ℕ, A.den = (A i j).den * t ∧
      A.num i j = (t : ℤ) * (A i j).num := by
  obtain ⟨t, ht⟩ := (Matrix.den_dvd_iff.mp (dvd_refl A.den)) i j
  refine ⟨t, ht, ?_⟩
  have hscalar : (A.den : ℚ) * A i j = ((t : ℤ) * (A i j).num : ℤ) := by
    calc
      (A.den : ℚ) * A i j = (t : ℚ) * (A i j * ((A i j).den : ℚ)) := by
        rw [ht, Nat.cast_mul]
        ring
      _ = (t : ℚ) * ((A i j).num : ℚ) := by rw [Rat.mul_den_eq_num]
      _ = ((t : ℤ) * (A i j).num : ℤ) := by push_cast; rfl
  simp only [Matrix.num, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
    hscalar, Rat.num_intCast]

theorem matrix_num_abs_le_den_mul {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) ℚ) (i : Fin r) (j : Fin n) :
    (A.num i j).natAbs ≤ A.den * (A i j).num.natAbs := by
  obtain ⟨t, ht, hn⟩ := matrix_num_eq_den_quotient_mul A i j
  have htd : t ≤ A.den := by
    calc
      t = 1*t := (one_mul t).symm
      _ ≤ (A i j).den*t := Nat.mul_le_mul_right t (A i j).den_pos
      _ = A.den := ht.symm
  rw [hn, Int.natAbs_mul, Int.natAbs_natCast]
  exact Nat.mul_le_mul_right _ htd

theorem matrix_num_bound_from_original_entries {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) ℚ) (P D : ℕ)
    (hP : ∀ i j, (A i j).num.natAbs ≤ P)
    (hD : ∀ i j, (A i j).den ≤ D) :
    ∀ i j, (A.num i j).natAbs ≤ P * D^(r*n) := by
  intro i j
  calc
    (A.num i j).natAbs ≤ A.den * (A i j).num.natAbs := matrix_num_abs_le_den_mul A i j
    _ ≤ D^(r*n) * P := Nat.mul_le_mul
      ((matrix_den_le_input_product A).trans (inputDenominatorProduct_le A D hD))
      (hP i j)
    _ = P * D^(r*n) := Nat.mul_comm _ _

def clearedInputExponent (r n B : ℕ) : ℕ := B * (r*n+1)

/-- Explicit original-entry bridge: no H bound on Matrix.num is supplied by
the caller. Its exponent is earned from at most r*n denominator factors. -/
theorem matrix_num_bound_from_input_bits {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) ℚ) (B : ℕ)
    (hnum : ∀ i j, (A i j).num.natAbs ≤ 2^B)
    (hden : ∀ i j, (A i j).den ≤ 2^B) :
    ∀ i j, (A.num i j).natAbs ≤ 2^(clearedInputExponent r n B) := by
  intro i j
  calc
    (A.num i j).natAbs ≤ 2^B * (2^B)^(r*n) :=
      matrix_num_bound_from_original_entries A (2^B) (2^B) hnum hden i j
    _ = (2^B)^(r*n+1) := by rw [pow_succ]; exact Nat.mul_comm _ _
    _ = 2^(clearedInputExponent r n B) := by rw [← pow_mul]; rfl

end SparseCompletion.Gaussian
