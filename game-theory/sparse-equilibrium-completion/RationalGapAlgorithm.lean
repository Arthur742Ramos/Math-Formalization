/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed.
Returns actual rational strategy/payoff data; Fourier–Motzkin cost may be exponential. -/
module
public import RationalGapRealDecision
public import RationalResidualGap
public import RationalGapSearch
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalGapAlgorithm {k m : ℕ} {I : Type*} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I m) :
    Option ((Fin m → ℚ) × (Fin m → Fin m → ℚ)) :=
  match rationalGapSolve K D p M r ρ η R with
  | none => none
  | some q => (rationalResidualCompletion q (rationalScore D p) M (ρ+η)).map (fun B => (q,B))

theorem rational_gap_algorithm_sound {k m : ℕ} {I : Type*} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I m) (q : Fin m → ℚ) (B : Fin m → Fin m → ℚ)
    (h : rationalGapAlgorithm K D p M r ρ η R=some (q,B)) :
    R.Satisfies q ∧ RationalGapConditions K D p q M r ρ η ∧
      ResidualRatConditions q (rationalScore D p) M (ρ+η) B := by
  cases hq : rationalGapSolve K D p M r ρ η R with
  | none => simp only [rationalGapAlgorithm,hq] at h; cases h
  | some y =>
    cases hB : rationalResidualCompletion y (rationalScore D p) M (ρ+η) with
    | none => simp only [rationalGapAlgorithm,hq,hB,Option.map_none] at h; cases h
    | some C =>
      have hp : (y,C)=(q,B) := Option.some.inj (by
        simpa only [rationalGapAlgorithm,hq,hB,Option.map_some] using h)
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj hp
      have hh := rational_gap_solve_sound K D p M r ρ η R y hq
      exact ⟨hh.2,(rational_gap_check_iff K D p y M r ρ η).mp hh.1,
        rational_residual_completion_rat_sound y (rationalScore D p) M (ρ+η) C hB⟩

theorem rational_gap_algorithm_complete {k m : ℕ} {I : Type*} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I m) (hM : 0 < M) (hη : 0 < η)
    (h : RationalGapExists K D p M r ρ η R) :
    ∃ q B, rationalGapAlgorithm K D p M r ρ η R=some (q,B) := by
  cases hq : rationalGapSolve K D p M r ρ η R with
  | none => exact False.elim ((rational_gap_solve_none_iff K D p M r ρ η R).mp hq h)
  | some q =>
    have hc := (rational_gap_solve_sound K D p M r ρ η R q hq).1
    obtain ⟨B,hB⟩ := rational_gap_reconstruction_complete K D p q M r ρ η hM hη hc
    change rationalResidualCompletion q (rationalScore D p) M (ρ+η)=some B at hB
    exact ⟨q,B,by simp only [rationalGapAlgorithm,hq,hB,Option.map_some]⟩

end SparseCompletion
