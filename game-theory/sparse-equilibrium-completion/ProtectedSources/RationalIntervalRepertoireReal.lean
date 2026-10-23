/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.RationalIntervalRepertoireSolver
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
theorem real_interval_repertoire_algorithm_success {k m : ℕ} {I : Type*} [Fintype I]
    (loK hiK : Fin k → Fin k → ℚ) (lo hi : Fin m → Fin k → ℚ) (p : Fin k → ℚ)
    (M r ρ η : ℚ) (R : RationalLinearSystem I (m+(m*k+(k*k+0*m)))) (K : Fin k → Fin k → ℝ) (D : Fin m → Fin k → ℝ)
    (q : Fin m → ℝ) (B : Fin m → Fin m → ℝ)
    (hM : 0 < M) (hη : 0 < η) (hlu : ∀ i a, lo i a ≤ hi i a)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ i, 0 ≤ q i) (hr : ∑ i, q i=(r : ℝ))
    (hK : IsSkew K) (hKb : ∀ a b, (loK a b : ℝ) ≤ K a b ∧ K a b ≤ (hiK a b : ℝ))
    (hD : ∀ i a, (lo i a : ℝ) ≤ D i a ∧ D i a ≤ (hi i a : ℝ))
    (hB : IsSkew B) (hb : ∀ i j, -(M : ℝ) ≤ B i j ∧ B i j ≤ (M : ℝ))
    (hrows : ∀ a, response (blockMatrix K D B) (blockWeights (fun a => (p a : ℝ)) q) a ≤ (ρ : ℝ))
    (hR : R.RealSatisfies (intervalPack q (fun i a => q i*D i a) K (H := 0) Fin.elim0)) :
    ∃ x C, rationalIntervalRepertoireAlgorithm loK hiK lo hi p M r ρ η R=some (x,C) := by
  obtain ⟨A,hA⟩ := real_interval_completion_physical_point loK hiK lo hi p M r ρ η
    K D q B hM hp hq hr hK hKb hD hB hb hrows
  apply rational_interval_repertoire_algorithm_real_complete loK hiK lo hi p M r ρ η R hM hη hlu
  refine ⟨intervalPack q (fun i a => q i*D i a) K A,
    (rational_interval_repertoire_real_system_iff loK hiK lo hi p M r ρ η R _).mpr ⟨?_,?_⟩⟩
  · apply (rational_interval_system_real_point loK hiK lo hi p M r ρ η _).mpr
    simpa only [interval_pack_q,interval_pack_v,interval_pack_k,interval_pack_aux] using hA
  · simpa only [interval_physical_pack] using hR

end SparseCompletion
