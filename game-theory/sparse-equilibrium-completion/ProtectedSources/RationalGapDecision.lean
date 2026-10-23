/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed.
The exact rational solver uses Fourier–Motzkin elimination; no polynomial cost. -/
module
public import ProtectedSources.RationalGapEncoding
public import ProtectedSources.RationalLinearSolver
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def RationalLinearSystem.append {I J : Type*} {n : ℕ}
    (S : RationalLinearSystem I n) (T : RationalLinearSystem J n) : RationalLinearSystem (I ⊕ J) n :=
  ⟨Sum.elim S.coefficient T.coefficient,Sum.elim S.rightSide T.rightSide⟩

theorem rational_linear_append_iff {I J : Type*} {n : ℕ}
    (S : RationalLinearSystem I n) (T : RationalLinearSystem J n) (q : Fin n → ℚ) :
    (S.append T).Satisfies q ↔ S.Satisfies q ∧ T.Satisfies q := by
  constructor
  · intro h
    exact ⟨fun i => h (.inl i),fun j => h (.inr j)⟩
  · rintro ⟨hS,hT⟩ a
    rcases a with i | j
    · exact hS i
    · exact hT j

def rationalGapSystem {k m : ℕ}
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ) (M r ρ η : ℚ) :
    RationalLinearSystem (RationalGapRow k m (rationalGridSize M r η)) m :=
  ⟨rationalGapCoefficient D p M r ρ η,rationalGapRightSide K D p M r ρ η⟩

def rationalGapSolve {k m : ℕ} {I : Type*} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ) (M r ρ η : ℚ)
    (R : RationalLinearSystem I m) : Option (Fin m → ℚ) :=
  rationalLPSolve m ((rationalGapSystem K D p M r ρ η).append R)

theorem rational_gap_solve_sound {k m : ℕ} {I : Type*} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ) (M r ρ η : ℚ)
    (R : RationalLinearSystem I m) (q : Fin m → ℚ)
    (h : rationalGapSolve K D p M r ρ η R=some q) :
    checkRationalGap K D p q M r ρ η=true ∧ R.Satisfies q := by
  have hh := (rational_linear_append_iff (rationalGapSystem K D p M r ρ η) R q).mp
    (rational_lp_solve_sound m _ q h)
  exact ⟨(rational_gap_linear_acceptance_iff K D p q M r ρ η).mpr hh.1,hh.2⟩

theorem rational_gap_solve_none_iff {k m : ℕ} {I : Type*} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ) (M r ρ η : ℚ)
    (R : RationalLinearSystem I m) :
    rationalGapSolve K D p M r ρ η R=none ↔
      ¬∃ q, RationalGapConditions K D p q M r ρ η ∧ R.Satisfies q := by
  rw [rationalGapSolve,rational_lp_solve_none_iff]
  apply not_congr
  apply exists_congr
  intro q
  rw [rational_linear_append_iff]
  exact and_congr (rational_gap_conditions_iff_linear K D p q M r ρ η).symm Iff.rfl

theorem rational_gap_solve_completed_witness {k m : ℕ} {I : Type*} [Fintype I]
    (K : Fin k → Fin k → ℚ) (D : Fin m → Fin k → ℚ) (p : Fin k → ℚ) (M r ρ η : ℚ)
    (R : RationalLinearSystem I m) (q : Fin m → ℚ) (hM : 0 < M) (hη : 0 < η)
    (h : rationalGapSolve K D p M r ρ η R=some q) :
    R.Satisfies q ∧ ∃ B : Fin m → Fin m → ℝ, IsSkew B ∧
      (∀ i j, -(M : ℝ) ≤ B i j ∧ B i j ≤ (M : ℝ)) ∧
      ∀ a, response (blockMatrix (fun h a => (K h a : ℝ)) (fun i h => (D i h : ℝ)) B)
        (blockWeights (fun h => (p h : ℝ)) (fun i => (q i : ℝ))) a ≤ (ρ : ℝ)+(η : ℝ) := by
  have hs := rational_gap_solve_sound K D p M r ρ η R q h
  exact ⟨hs.2,rational_gap_completed_witness K D p q M r ρ η hM hη hs.1⟩

end SparseCompletion
