/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed.
Rational Fourier–Motzkin completeness across the rational-to-real embedding. -/
module
public import ProtectedSources.RationalLinearReal
public import ProtectedSources.RationalLinearSolver
@[expose] public section
namespace SparseCompletion
universe u

theorem rational_lp_real_complete (n : ℕ) {I : Type u} [Fintype I]
    (S : RationalLinearSystem I n) (h : ∃ x, S.RealSatisfies x) :
    ∃ q, rationalLPSolve n S=some q := by
  induction n generalizing I with
  | zero =>
    obtain ⟨x,hx⟩ := h
    have hr := (rational_linear_real_zero_iff S x).mp hx
    exact ⟨Fin.elim0,by simp [rationalLPSolve,hr]⟩
  | succ n ih =>
    obtain ⟨x,hx⟩ := h
    have hr := rational_linear_real_reduce_feasible S x hx
    obtain ⟨y,hy⟩ := ih S.reduce ⟨fun j => x j.succ,hr⟩
    exact ⟨Fin.cons (α := fun _ => ℚ)
      (RationalElimination.generalCandidate S.slope (S.rest y) S.rightSide) y,
      by simp only [rationalLPSolve,hy]⟩

theorem rational_linear_real_feasible_iff {I : Type*} [Fintype I] {n : ℕ}
    (S : RationalLinearSystem I n) :
    (∃ x, S.RealSatisfies x) ↔ ∃ q, S.Satisfies q := by
  constructor
  · intro h
    obtain ⟨q,hq⟩ := rational_lp_real_complete n S h
    exact ⟨q,rational_lp_solve_sound n S q hq⟩
  · rintro ⟨q,hq⟩
    exact ⟨fun j => (q j : ℝ),(rational_linear_real_cast_iff S q).mpr hq⟩

theorem rational_lp_solve_none_iff_real (n : ℕ) {I : Type u} [Fintype I]
    (S : RationalLinearSystem I n) :
    rationalLPSolve n S=none ↔ ¬∃ x, S.RealSatisfies x := by
  rw [rational_lp_solve_none_iff]
  exact not_congr (rational_linear_real_feasible_iff S).symm

/-- Computed from rational coefficients and the verified rational algorithm;
no decision procedure for arbitrary real comparisons is assumed. -/
def rationalLPRealFeasibleDecidable (n : ℕ) {I : Type u} [Fintype I]
    (S : RationalLinearSystem I n) : Decidable (∃ x, S.RealSatisfies x) :=
  match he : rationalLPSolve n S with
  | none => isFalse ((rational_lp_solve_none_iff_real n S).mp he)
  | some q => isTrue ⟨fun j => (q j : ℝ),(rational_linear_real_cast_iff S q).mpr
      (rational_lp_solve_sound n S q he)⟩

end SparseCompletion
