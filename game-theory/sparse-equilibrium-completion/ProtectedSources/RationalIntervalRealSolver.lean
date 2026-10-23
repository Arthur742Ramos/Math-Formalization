/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.RationalIntervalRealNecessity
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem rational_interval_algorithm_real_lp_complete {k m : ℕ}
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (hM : 0 < M) (hη : 0 < η) (hlu : ∀ i a, lo i a ≤ hi i a)
    (hf : ∃ x, (rationalIntervalSystem loK hiK lo hi p M r ρ η).RealSatisfies x) :
    ∃ x B, rationalIntervalAlgorithm loK hiK lo hi p M r ρ η=some (x,B) := by
  apply rational_interval_algorithm_complete loK hiK lo hi p M r ρ η hM hη hlu
  exact (rational_interval_lp_feasible_iff loK hiK lo hi p M r ρ η).mp
    ((rational_linear_real_feasible_iff _).mp hf)

theorem real_interval_completion_algorithm_success {k m : ℕ}
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (K : Fin k → Fin k → ℝ) (D : Fin m → Fin k → ℝ)
    (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ)
    (hM : 0 < M) (hη : 0 < η) (hlu : ∀ i a, lo i a ≤ hi i a)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ i, 0 ≤ q i) (hr : ∑ i, q i=(r : ℝ))
    (hK : IsSkew K) (hKb : ∀ a b, (loK a b : ℝ) ≤ K a b ∧ K a b ≤ (hiK a b : ℝ))
    (hD : ∀ i a, (lo i a : ℝ) ≤ D i a ∧ D i a ≤ (hi i a : ℝ))
    (hB : IsSkew B) (hb : ∀ i j, -(M : ℝ) ≤ B i j ∧ B i j ≤ (M : ℝ))
    (hrows : ∀ a, response (blockMatrix K D B) (blockWeights (fun a => (p a : ℝ)) q) a ≤ (ρ : ℝ)) :
    ∃ x C, rationalIntervalAlgorithm loK hiK lo hi p M r ρ η=some (x,C) := by
  exact rational_interval_algorithm_real_lp_complete loK hiK lo hi p M r ρ η hM hη hlu
    (real_interval_completion_rational_lp loK hiK lo hi p M r ρ η K D q B hM hp hq hr hK hKb hD hB hb hrows)

end SparseCompletion
