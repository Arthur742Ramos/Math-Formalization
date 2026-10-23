/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed.
Classical Fourier–Motzkin elimination; this can have exponential size. -/
module
public import ProtectedSources.RationalLinearSystem
public import ProtectedSources.RationalOneVariableFintype
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
universe u

/-- Exact rational feasibility by dimension recursion and genuine finite elimination.
This is not a polynomial-time LP theorem. -/
def rationalLPSolve : (n : ℕ) → {I : Type u} → [Fintype I] →
    RationalLinearSystem I n → Option (Fin n → ℚ)
  | 0, _, _, S => if ∀ i, 0 ≤ S.rightSide i then some Fin.elim0 else none
  | n+1, _, _, S => match rationalLPSolve n S.reduce with
    | none => none
    | some q => some (Fin.cons (α := fun _ => ℚ)
        (RationalElimination.generalCandidate S.slope (S.rest q) S.rightSide) q)

theorem rational_linear_eliminated_exists {I : Type*} [Fintype I] {n : ℕ}
    (S : RationalLinearSystem I (n+1)) (q : Fin n → ℚ) :
    S.Eliminated q ↔ ∃ x : ℚ, S.Satisfies (Fin.cons (α := fun _ => ℚ) x q) := by
  have he : S.Eliminated q ↔
      RationalElimination.FintypeEliminated S.slope (S.rest q) S.rightSide := Iff.rfl
  rw [he,RationalElimination.fintype_eliminated_iff_exists]
  simp only [rational_linear_cons_iff]

theorem rational_lp_solve_sound (n : ℕ) {I : Type u} [Fintype I]
    (S : RationalLinearSystem I n) (q : Fin n → ℚ) (h : rationalLPSolve n S=some q) :
    S.Satisfies q := by
  induction n generalizing I with
  | zero =>
    unfold rationalLPSolve at h
    split at h
    next hh =>
      intro i
      simpa using hh i
    next hh => simp at h
  | succ n ih =>
    cases he : rationalLPSolve n S.reduce with
    | none => simp [rationalLPSolve,he] at h
    | some y =>
      have hy := ih S.reduce y he
      have hel := (rational_linear_reduce_iff S y).mp hy
      have hx := RationalElimination.fintype_candidate_feasible S.slope (S.rest y) S.rightSide hel
      have hq : Fin.cons (α := fun _ => ℚ)
          (RationalElimination.generalCandidate S.slope (S.rest y) S.rightSide) y=q := by
        exact Option.some.inj (by simpa only [rationalLPSolve,he] using h)
      rw [←hq]
      exact (rational_linear_cons_iff S y _).mpr hx


theorem rational_linear_decomposition {n : ℕ} (q : Fin (n+1) → ℚ) :
    Fin.cons (α := fun _ => ℚ) (q 0) (fun j => q j.succ)=q := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem rational_lp_solve_complete (n : ℕ) {I : Type u} [Fintype I]
    (S : RationalLinearSystem I n) (h : ∃ q, S.Satisfies q) :
    ∃ q, rationalLPSolve n S=some q := by
  induction n generalizing I with
  | zero =>
    obtain ⟨q,hq⟩ := h
    have hr : ∀ i, 0 ≤ S.rightSide i := by
      intro i
      simpa using hq i
    exact ⟨Fin.elim0,by simp [rationalLPSolve,hr]⟩
  | succ n ih =>
    obtain ⟨q,hq⟩ := h
    have hc : S.Satisfies (Fin.cons (α := fun _ => ℚ) (q 0) (fun j => q j.succ)) := by
      rw [rational_linear_decomposition]
      exact hq
    have hel := (rational_linear_eliminated_exists S (fun j => q j.succ)).mpr ⟨q 0,hc⟩
    have hr := (rational_linear_reduce_iff S (fun j => q j.succ)).mpr hel
    obtain ⟨y,hy⟩ := ih S.reduce ⟨fun j => q j.succ,hr⟩
    exact ⟨Fin.cons (α := fun _ => ℚ)
      (RationalElimination.generalCandidate S.slope (S.rest y) S.rightSide) y,
      by simp only [rationalLPSolve,hy]⟩

theorem rational_lp_solve_none_iff (n : ℕ) {I : Type u} [Fintype I]
    (S : RationalLinearSystem I n) :
    rationalLPSolve n S=none ↔ ¬∃ q, S.Satisfies q := by
  constructor
  · intro hn hf
    obtain ⟨q,hq⟩ := rational_lp_solve_complete n S hf
    rw [hn] at hq
    cases hq
  · intro hn
    cases he : rationalLPSolve n S with
    | none => rfl
    | some q => exact False.elim (hn ⟨q,rational_lp_solve_sound n S q he⟩)

/-- Genuine decidability proved from the total rational elimination algorithm. -/
def rationalLPFeasibleDecidable (n : ℕ) {I : Type u} [Fintype I]
    (S : RationalLinearSystem I n) : Decidable (∃ q, S.Satisfies q) :=
  match he : rationalLPSolve n S with
  | none => isFalse ((rational_lp_solve_none_iff n S).mp he)
  | some q => isTrue ⟨q,rational_lp_solve_sound n S q he⟩

end SparseCompletion
