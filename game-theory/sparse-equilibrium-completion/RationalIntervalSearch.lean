/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import RationalIntervalMonotone
public import Bisection
@[expose] public section
namespace SparseCompletion

def RationalIntervalFeasible {k m : ℕ} {I : Type*}
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I (m+(m*k+(k*k+0*m)))) : Prop :=
  ∃ x, (rationalIntervalRepertoireSystem loK hiK lo hi p M r ρ η R).Satisfies x

instance rationalIntervalFeasibleDecidable {k m : ℕ} {I : Type*} [Fintype I]
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I (m+(m*k+(k*k+0*m)))) :
    Decidable (RationalIntervalFeasible loK hiK lo hi p M r ρ η R) :=
  let S := rationalIntervalRepertoireSystem loK hiK lo hi p M r ρ η R
  (Option.rec (motive := fun o => rationalLPSolve _ S=o →
      Decidable (RationalIntervalFeasible loK hiK lo hi p M r ρ η R))
    (fun he => isFalse ((rational_lp_solve_none_iff _ S).mp he))
    (fun x he => isTrue ⟨x,rational_lp_solve_sound _ S x he⟩)
    (rationalLPSolve _ S)) rfl

def rationalIntervalSearch {k m : ℕ} {I : Type*} [Fintype I]
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r η : ℚ) (R : RationalLinearSystem I (m+(m*k+(k*k+0*m)))) (n : ℕ) : ℚ × ℚ :=
  RationalBisection.search (fun ρ => RationalIntervalFeasible loK hiK lo hi p M r ρ η R) n 0 M

theorem rational_interval_search_bracket {k m : ℕ} {I : Type*} [Fintype I]
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r η : ℚ) (R : RationalLinearSystem I (m+(m*k+(k*k+0*m)))) (n : ℕ)
    (hM : 0 ≤ M) (hupper : RationalIntervalFeasible loK hiK lo hi p M r M η R) :
    let z := rationalIntervalSearch loK hiK lo hi p M r η R n
    0 ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ M ∧ RationalIntervalFeasible loK hiK lo hi p M r z.2 η R ∧
      (z.1=0 ∨ ¬RationalIntervalFeasible loK hiK lo hi p M r z.1 η R) ∧
      z.2-z.1 ≤ M/((2 : ℕ) : ℚ)^n := by
  simpa only [rationalIntervalSearch,sub_zero] using
    RationalBisection.search_spec (fun ρ => RationalIntervalFeasible loK hiK lo hi p M r ρ η R) n 0 M hM hupper

def rationalIntervalApproximation {k m : ℕ} {I : Type*} [Fintype I]
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r η : ℚ) (R : RationalLinearSystem I (m+(m*k+(k*k+0*m)))) (n : ℕ) :
    Option ((ℚ × ℚ) × ((Fin (m+(m*k+(k*k+rationalGridSize M r η*m))) → ℚ) ×
      (Fin m → Fin m → ℚ))) :=
  let z := rationalIntervalSearch loK hiK lo hi p M r η R n
  (rationalIntervalRepertoireAlgorithm loK hiK lo hi p M r z.2 η R).map (fun w => (z,w))

theorem rational_interval_approximation_complete {k m : ℕ} {I : Type*} [Fintype I]
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r η : ℚ) (R : RationalLinearSystem I (m+(m*k+(k*k+0*m)))) (n : ℕ)
    (hM : 0 < M) (hη : 0 < η) (hlu : ∀ i a, lo i a ≤ hi i a)
    (hupper : RationalIntervalFeasible loK hiK lo hi p M r M η R) :
    ∃ z x B, rationalIntervalApproximation loK hiK lo hi p M r η R n=some (z,(x,B)) := by
  have hz := rational_interval_search_bracket loK hiK lo hi p M r η R n (le_of_lt hM) hupper
  let z := rationalIntervalSearch loK hiK lo hi p M r η R n
  have hf := (rational_linear_real_feasible_iff _).mpr hz.2.2.2.1
  obtain ⟨x,B,hout⟩ := rational_interval_repertoire_algorithm_real_complete loK hiK lo hi p M r z.2 η R hM hη hlu hf
  dsimp only [z] at hout
  exact ⟨rationalIntervalSearch loK hiK lo hi p M r η R n,x,B,by
    simp only [rationalIntervalApproximation,hout,Option.map_some]⟩

end SparseCompletion
