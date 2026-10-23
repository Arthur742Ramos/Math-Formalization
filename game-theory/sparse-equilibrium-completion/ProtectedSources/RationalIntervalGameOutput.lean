/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.RationalIntervalSolver
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem rational_interval_algorithm_full_game {k m : ℕ}
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (hη : 0 < η) (hp : ∀ a, 0 ≤ p a) (hnorm : (∑ a, p a)+r=1)
    (hloK : ∀ a b, -M ≤ loK a b) (hhiK : ∀ a b, hiK a b ≤ M)
    (hlo : ∀ i a, -M ≤ lo i a) (hhi : ∀ i a, hi i a ≤ M)
    (hlu : ∀ i a, lo i a ≤ hi i a)
    (x : Fin (m+(m*k+(k*k+rationalGridSize M r η*m))) → ℚ)
    (B : Fin m → Fin m → ℚ)
    (hout : rationalIntervalAlgorithm loK hiK lo hi p M r ρ η=some (x,B)) :
    let q := intervalQ x
    let K := intervalK x
    let D := rationalIntervalRecover lo (intervalV x) q
    (∀ a b, loK a b ≤ K a b ∧ K a b ≤ hiK a b) ∧
    (∀ i a, lo i a ≤ D i a ∧ D i a ≤ hi i a) ∧
    (∀ a, 0 ≤ blockWeights (fun a => (p a : ℝ)) (fun i => (q i : ℝ)) a) ∧
    (∑ a, blockWeights (fun a => (p a : ℝ)) (fun i => (q i : ℝ)) a)=1 ∧
    IsSkew (blockMatrix (fun a b => (K a b : ℝ)) (fun i a => (D i a : ℝ))
      (fun i j => (B i j : ℝ))) ∧
    (∀ a b, -(M : ℝ) ≤ blockMatrix (fun a b => (K a b : ℝ)) (fun i a => (D i a : ℝ))
      (fun i j => (B i j : ℝ)) a b ∧
      blockMatrix (fun a b => (K a b : ℝ)) (fun i a => (D i a : ℝ))
      (fun i j => (B i j : ℝ)) a b ≤ (M : ℝ)) ∧
    ∀ a, response (blockMatrix (fun a b => (K a b : ℝ)) (fun i a => (D i a : ℝ))
      (fun i j => (B i j : ℝ))) (blockWeights (fun a => (p a : ℝ)) (fun i => (q i : ℝ))) a ≤
        (ρ : ℝ)+(η : ℝ) := by
  obtain ⟨hpoint,hB⟩ := rational_interval_algorithm_output loK hiK lo hi p M r ρ η x B hout
  obtain ⟨hK,hKb,hgap⟩ := rational_interval_point_gap loK hiK lo hi _ _ p _ M r ρ η _ hpoint
  obtain ⟨hD,hG⟩ := rational_interval_gap_recovered _ lo hi _ p _ M r ρ η hlu hgap
  refine ⟨hKb,hD,?_⟩
  apply rational_gap_reconstruction_normalized_full_game _ _ p _ M r ρ η hη hp hnorm hK
    (fun a b => ⟨le_trans (hloK a b) (hKb a b).1,le_trans (hKb a b).2 (hhiK a b)⟩)
    (fun i a => ⟨le_trans (hlo i a) (hD i a).1,le_trans (hD i a).2 (hhi i a)⟩)
    ((rational_gap_check_iff _ _ _ _ _ _ _ _).mpr hG) B hB

end SparseCompletion
