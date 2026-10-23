/- AI-assisted formalization; Apache-2.0, following the parent repository.
Strict module compilation and artifact evidence are retained in attempts/.
These are explicit arithmetic bounds, not an assumed polynomial solver or a
runtime invariant supplied by the caller. The elimination-to-minor invariant
needed to apply them at every Gaussian stage remains an open proof obligation.
-/
module
public import ProtectedSources.RationalGaussianKernel
public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
public import Mathlib.LinearAlgebra.Matrix.Integer
@[expose] public section
open scoped BigOperators
namespace SparseCompletion.Gaussian

/-- Reduction of a rational quotient cannot increase its numerator height. -/
theorem quotient_num_height (a b : ℤ) (hb : b ≠ 0) :
    ((a : ℚ) / (b : ℚ)).num.natAbs ≤ a.natAbs := by
  by_cases ha : a = 0
  · simp [ha]
  · apply Int.natAbs_le_of_dvd_ne_zero _ ha
    simpa only [Rat.divInt_eq_div] using Rat.num_dvd a hb

/-- The reduced denominator divides the original denominator and is no larger. -/
theorem quotient_den_height (a b : ℤ) (hb : b ≠ 0) :
    ((a : ℚ) / (b : ℚ)).den ≤ b.natAbs := by
  have h := Int.natAbs_le_of_dvd_ne_zero (Rat.den_dvd a b) hb
  simpa only [Int.natAbs_natCast, Rat.divInt_eq_div] using h

/-- Leibniz's bound is sufficient for polynomial bit height; Hadamard's sharper
bound is unnecessary. This uses the pinned Mathlib determinant bound. -/
theorem determinant_height {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (H : ℕ) (hA : ∀ i j, (A i j).natAbs ≤ H) :
    A.det.natAbs ≤ n.factorial * H^n := by
  have hentry : ∀ i j, |A i j| ≤ (H : ℤ) := by
    intro i j
    rw [← Int.natCast_natAbs]
    exact_mod_cast hA i j
  have hd := Matrix.det_le (A := A) (abv := AbsoluteValue.abs) hentry
  have hz : |A.det| ≤ (n.factorial : ℤ) * (H : ℤ)^n := by
    simpa only [AbsoluteValue.abs_apply, Fintype.card_fin, nsmul_eq_mul] using hd
  rw [← Int.natCast_natAbs] at hz
  exact_mod_cast hz

/-- Concrete minor quotient bound. When U,V are (k+1)- and k-minors of a
cleared input matrix, this gives both encoding components, with no coprimality
hypothesis and no lower bound on the absolute value of a rational pivot. -/
theorem minor_quotient_height {u v : ℕ}
    (U : Matrix (Fin u) (Fin u) ℤ) (V : Matrix (Fin v) (Fin v) ℤ)
    (H : ℕ) (hU : ∀ i j, (U i j).natAbs ≤ H)
    (hV : ∀ i j, (V i j).natAbs ≤ H) (hv : V.det ≠ 0) :
    (((U.det : ℚ) / (V.det : ℚ)).num.natAbs ≤ u.factorial * H^u) ∧
      (((U.det : ℚ) / (V.det : ℚ)).den ≤ v.factorial * H^v) := by
  exact ⟨(quotient_num_height U.det V.det hv).trans (determinant_height U H hU),
    (quotient_den_height U.det V.det hv).trans (determinant_height V H hV)⟩

/-- Every displayed submatrix inherits the input coefficient height. Maps need
not be injective: the bound also covers repeated rows or columns and det = 0. -/
theorem submatrix_determinant_height {r n k : ℕ}
    (Z : Matrix (Fin r) (Fin n) ℤ) (H : ℕ)
    (hZ : ∀ i j, (Z i j).natAbs ≤ H)
    (rows : Fin k → Fin r) (cols : Fin k → Fin n) :
    (Z.submatrix rows cols).det.natAbs ≤ k.factorial * H^k := by
  exact determinant_height _ H (fun i j => hZ (rows i) (cols j))

/-- Pivot ratios cancel a shared minor denominator. This prevents a spurious
extra denominator factor when bounding the coefficients used by lift. -/
theorem shared_denominator_ratio (a b δ : ℤ) (ha : a ≠ 0) (hδ : δ ≠ 0) :
    ((b : ℚ) / (δ : ℚ)) / ((a : ℚ) / (δ : ℚ)) =
      (b : ℚ) / (a : ℚ) := by
  have haq : (a : ℚ) ≠ 0 := Int.cast_ne_zero.mpr ha
  have hδq : (δ : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hδ
  field_simp [haq, hδq]

theorem shared_minor_pivot_ratio_height {k : ℕ}
    (U V : Matrix (Fin k) (Fin k) ℤ) (δ : ℤ)
    (H : ℕ) (hU : ∀ i j, (U i j).natAbs ≤ H)
    (hV : ∀ i j, (V i j).natAbs ≤ H) (hv : V.det ≠ 0) (hδ : δ ≠ 0) :
    ((((U.det : ℚ) / (δ : ℚ)) / ((V.det : ℚ) / (δ : ℚ))).num.natAbs ≤
      k.factorial * H^k) ∧
    ((((U.det : ℚ) / (δ : ℚ)) / ((V.det : ℚ) / (δ : ℚ))).den ≤
      k.factorial * H^k) := by
  rw [shared_denominator_ratio V.det U.det δ hv hδ]
  exact minor_quotient_height U V H hU hV hv

/-- Exact algebraic induction step for bordered minors. To apply this to the
program, a Sylvester determinant identity must establish hminor for its actual
selected rows and prefix columns. This lemma does not assume such an invariant
of kernel, and is not itself the missing determinant identity. -/
theorem residual_shared_minor_step (a b c d δ e : ℚ)
    (ha : a ≠ 0) (hδ : δ ≠ 0) (hminor : a*d-c*b = δ*e) :
    d/δ - (c/δ) * ((b/δ)/(a/δ)) = e/a := by
  calc
    d/δ - (c/δ) * ((b/δ)/(a/δ)) = (a*d-c*b)/(δ*a) := by
      field_simp [ha, hδ]
    _ = (δ*e)/(δ*a) := by rw [hminor]
    _ = e/a := by
      field_simp [ha, hδ]


/-- Clearing a rational matrix's single common denominator preserves exactly
its homogeneous equations. The denominator is Mathlib's finite LCM, not an
oracle or a supplied integer encoding. -/
theorem clear_denominators_kernel_iff {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) ℚ) (w : Fin n → ℚ) :
    (∀ i, ∑ j, (A.num i j : ℚ) * w j = 0) ↔
      ∀ i, ∑ j, A i j * w j = 0 := by
  have hD : (A.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr A.den_ne_zero
  have hrow : ∀ i, (∑ j, (A.num i j : ℚ) * w j) / A.den =
      ∑ j, A i j * w j := by
    intro i
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    rw [← div_mul_eq_mul_div₀, Matrix.num_div_den]
  constructor
  · intro h i
    rw [← hrow i, h i, zero_div]
  · intro h i
    exact (div_eq_zero_iff.mp (by rw [hrow i, h i])).resolve_right hD

/-- A single residual update with a scalar integer denominator is the 2x2
minor formula. Higher-stage bordered-minor identities are still required. -/
theorem integer_first_residual (a b c d : ℤ) (ha : a ≠ 0) :
    (d : ℚ) - (c : ℚ) * ((b : ℚ) / (a : ℚ)) =
      ((a*d-c*b : ℤ) : ℚ) / (a : ℚ) := by
  have haq : (a : ℚ) ≠ 0 := Int.cast_ne_zero.mpr ha
  push_cast
  field_simp [haq]

/-- The residual's pivot row is exactly zero, including empty column sets. -/
theorem residual_pivot_row_zero {r n : ℕ}
    (A : Fin r → Fin (n+1) → ℚ) (p : Fin r) (hp : A p 0 ≠ 0) :
    ∀ j, residual A p p j = 0 := by
  intro j
  simp only [residual]
  field_simp [hp]; ring

/-- Previously zero rows remain zero. Together with deterministic nonzero-pivot
selection, this is the local fact needed to prove pivot rows never repeat. -/
theorem residual_preserves_zero_row {r n : ℕ}
    (A : Fin r → Fin (n+1) → ℚ) (p i : Fin r)
    (hi : ∀ j, A i j = 0) : ∀ j, residual A p i j = 0 := by
  intro j
  simp [residual, hi]

end SparseCompletion.Gaussian
