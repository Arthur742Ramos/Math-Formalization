/- AI-assisted Gaussian global-height continuation; Apache-2.0.
Exact check status is recorded in source-bound receipts outside this source.
The original uncompiled v1 draft is preserved in source-global-height-v1.
Frozen Gaussian kernel APIs are unchanged. No bit-cost or general LP claim.
-/
module
public import ProtectedSources.GaussianTerminalTrace
public import Mathlib.LinearAlgebra.Matrix.Adjugate
@[expose] public section
open scoped BigOperators Matrix
namespace SparseCompletion.Gaussian

/-- Cramer's identity in the direction needed for an already computed vector.
Unlike inversion, this identity also covers singular and empty squares. -/
theorem det_smul_eq_cramer_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℚ) (x : ι → ℚ) :
    C.det • x = C.cramer (C *ᵥ x) := by
  symm
  rw [Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec_mulVec,
    Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]

/-- A generic algebra helper. The actual-output theorem below derives this
system and nonsingularity from real program steps rather than assuming them. -/
theorem integer_system_cramer {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℤ) (b : ι → ℤ) (x : ι → ℚ)
    (hdet : U.det ≠ 0)
    (hsolve : (fun i j => (U i j : ℚ)) *ᵥ x = fun i => (b i : ℚ)) :
    ∀ j, x j = ((U.updateCol j b).det : ℚ) / (U.det : ℚ) := by
  classical
  intro j
  have hd : (U.det : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hdet
  let C : Matrix ι ι ℚ := fun i j => (U i j : ℚ)
  have hm : (fun i j' => ((U.updateCol j b) i j' : ℚ)) =
      C.updateCol j (fun i => (b i : ℚ)) := by
    ext i j'
    simp only [Matrix.updateCol_apply]
    split_ifs <;> rfl
  have hs : C *ᵥ x = fun i => (b i : ℚ) := hsolve
  have hc := det_smul_eq_cramer_mulVec C x
  rw [hs] at hc
  have hh : C.det * x j = (C.updateCol j (fun i => (b i : ℚ))).det := congrFun hc j
  have hdC : C.det = (U.det : ℚ) := intCast_det U
  have hdM : (C.updateCol j (fun i => (b i : ℚ))).det =
      ((U.updateCol j b).det : ℚ) := by
    rw [← hm]
    exact intCast_det (U.updateCol j b)
  rw [hdC, hdM] at hh
  apply (eq_div_iff hd).mpr
  simpa only [mul_comm] using hh

theorem integer_system_coordinate_height {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℤ) (b : ι → ℤ) (x : ι → ℚ) (H : ℕ)
    (hU : ∀ i j, (U i j).natAbs ≤ H) (hb : ∀ i, (b i).natAbs ≤ H)
    (hdet : U.det ≠ 0)
    (hsolve : (fun i j => (U i j : ℚ)) *ᵥ x = fun i => (b i : ℚ)) :
    ∀ j, (x j).num.natAbs ≤ (Fintype.card ι).factorial * H^(Fintype.card ι) ∧
      (x j).den ≤ (Fintype.card ι).factorial * H^(Fintype.card ι) := by
  classical
  intro j
  rw [integer_system_cramer U b x hdet hsolve j]
  apply minor_quotient_height_any (U.updateCol j b) U H _ hU hdet
  intro i t
  by_cases ht : t = j
  · simpa only [Matrix.updateCol_apply, ite_eq_left ht] using hb i
  · simpa only [Matrix.updateCol_apply, ite_eq_right ht] using hU i t

/-- Actual normalized-output bound. The only data hypothesis is an
entry bound on the integer INPUT. The returned vector, actual terminal prefix,
nonsingular selected square, original-row equations and Cramer numerators are
all earned from the actual deterministic kernel success equation.

The max with one is essential: an empty pivot prefix returns a unit coordinate,
and zero coordinates have denominator one even when H=0. k<N also excludes
zero-column success, while k≤r is earned from actual distinct selected rows.
Exact check status is recorded in source-bound receipts. -/
theorem kernel_integer_output_height {r N : ℕ}
    (Z : Fin r → Fin N → ℤ) (H : ℕ) (hZ : ∀ i j, (Z i j).natAbs ≤ H)
    (w : QVec N)
    (hkernel : kernel r N (tableOfFn (fun i j => (Z i j : ℚ))) = some w) :
    ∃ k : ℕ, k ≤ r ∧ k < N ∧
      ∀ j, (w.get j).num.natAbs ≤ max 1 (k.factorial * H^k) ∧
        (w.get j).den ≤ max 1 (k.factorial * H^k) := by
  classical
  let A : QTable r N := tableOfFn (fun i j => (Z i j : ℚ))
  obtain ⟨k, n, P, Q, σ, B, hs, _hstop, hkN, hkr, hf, hz⟩ :=
    kernel_terminal_data A w hkernel
  let U : Matrix (PrefixIndex k) (PrefixIndex k) ℤ := Matrix.submatrix Z P Q
  let b : PrefixIndex k → ℤ := fun s => -Z (P s) (σ 0)
  let x : PrefixIndex k → ℚ := fun t => w.get (Q t)
  have hcast : selectedBlock (entry A) P Q = fun i j => (U i j : ℚ) := by
    ext i j
    change entry (tableOfFn (fun i j => (Z i j : ℚ))) (P i) (Q j) = (Z (P i) (Q j) : ℚ)
    exact entry_tableOfFn _ _ _
  have hdet : U.det ≠ 0 := by
    intro hh
    have hd := (minorStage_invariant hs).1
    apply hd
    rw [hcast, intCast_det, hh, Int.cast_zero]
  have hsolve : (fun i j => (U i j : ℚ)) *ᵥ x = fun i => (b i : ℚ) := by
    have he := terminal_prefix_equation hs w.get
      (kernel_sound r N A w hkernel).1 hf hz
    simpa only [hcast, x, b, A, entry_tableOfFn, Int.cast_neg] using he
  have hcoord := integer_system_coordinate_height U b x H
    (fun i j => hZ (P i) (Q j))
    (fun i => by simpa only [b, Int.natAbs_neg] using hZ (P i) (σ 0))
    hdet hsolve
  have hselected : ∀ t, (w.get (Q t)).num.natAbs ≤ k.factorial * H^k ∧
      (w.get (Q t)).den ≤ k.factorial * H^k := by
    simpa only [x, prefixIndex_card] using hcoord
  have hremaining : ∀ t, (w.get (σ t)).num.natAbs ≤ max 1 (k.factorial * H^k) ∧
      (w.get (σ t)).den ≤ max 1 (k.factorial * H^k) := by
    refine Fin.cases ?_ ?_
    · rw [hf]
      simp
    · intro j
      rw [hz j]
      constructor
      · simp
      · simp
  refine ⟨k, hkr, hkN, ?_⟩
  intro j
  obtain ⟨t, ht⟩ := (minorStage_columns_bijective hs).2 j
  rcases t with t | t
  · change Q t = j at ht
    rw [← ht]
    exact ⟨(hselected t).1.trans (le_max_right _ _),
      (hselected t).2.trans (le_max_right _ _)⟩
  · change σ t = j at ht
    rw [← ht]
    exact hremaining t

/-- Rational-input execution transfer. H bounds the actual integer
numerator matrix supplied by Matrix.num, whose common-denominator scaling is
proved to preserve every coefficient of the actual return value. This is not
yet an input-bit-size estimate: that separate encoding bridge remains open. -/
theorem kernel_rational_output_height {r N : ℕ}
    (A : QTable r N) (H : ℕ)
    (hH : ∀ i j, (Matrix.num (entry A) i j).natAbs ≤ H)
    (w : QVec N) (hkernel : kernel r N A = some w) :
    ∃ k : ℕ, k ≤ r ∧ k < N ∧
      ∀ j, (w.get j).num.natAbs ≤ max 1 (k.factorial * H^k) ∧
        (w.get j).den ≤ max 1 (k.factorial * H^k) := by
  have hi : kernel r N (integerNumeratorTable A) = some w := by
    rw [kernel_integerNumeratorTable]
    exact hkernel
  exact kernel_integer_output_height (Matrix.num (entry A)) H hH w hi

end SparseCompletion.Gaussian
