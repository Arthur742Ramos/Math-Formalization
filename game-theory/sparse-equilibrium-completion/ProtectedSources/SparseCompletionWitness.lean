/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.CompletionCriterion
public import ProtectedSources.GameSparseWitness

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

/-- A moment-preserving sparse witness with a reconstructed bounded skew
    completion. Every original row is retained in the response inequality. -/
theorem game_sparse_completion {ι : Type*} [Fintype ι]
    (k : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ) (B : ι → ι → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r ρ η : ℝ)
    (hM : 0 < M) (hr : 0 < r) (hη : 0 < η)
    (hq : ∀ i, 0 ≤ q i) (hmass : ∑ i, q i = r)
    (hB : IsSkew B) (hbound : ∀ i j, -M ≤ B i j)
    (hresp : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ρ) :
    ∃ (q' : ι → ℝ) (B' : ι → ι → ℝ),
      (∀ i, 0 ≤ q' i) ∧ (∑ i, q' i = r) ∧
      (∀ i, q i = 0 → q' i = 0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤ k+1+gridSize M r η ∧
      (∀ h, anchorResponse K D p q' h = anchorResponse K D p q h) ∧
      IsSkew B' ∧ (∀ i j, -M ≤ B' i j ∧ B' i j ≤ M) ∧
      (∀ a, response (blockMatrix K D B') (blockWeights p q') a ≤ ρ+η) := by
  classical
  obtain ⟨q', hq', hm', hs, hn, ha, hg, hc⟩ :=
    game_sparse_cut_certificate k K D B p q M r ρ η hM hr hη hq hmass hB hbound hresp
  obtain ⟨B', hsk', hb', hres'⟩ := completion_of_cuts_and_guards q' (score D p)
    M r (ρ+η) (le_of_lt hM) hq' hm' hc hg
  refine ⟨q', B', hq', hm', hs, hn, ha, hsk', hb', ?_⟩
  apply (block_response_bounds_iff K D B' p q' (ρ+η)).mpr
  refine ⟨?_, hres'⟩
  intro h
  rw [ha h]
  have hh := ((block_response_bounds_iff K D B p q ρ).mp hresp).1 h
  linarith

/-- Exact equilibria save the bottom hinge constraint, hence one support
    point, while still producing an actual completion on all original rows. -/
theorem exact_game_sparse_completion {ι : Type*} [Fintype ι]
    (k : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ) (B : ι → ι → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r η : ℝ)
    (hM : 0 < M) (hr : 0 < r) (hη : 0 < η)
    (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i) (hmass : ∑ i, q i = r)
    (hK : IsSkew K) (hB : IsSkew B) (hbound : ∀ i j, -M ≤ B i j ∧ B i j ≤ M)
    (hresp : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ 0) :
    ∃ (q' : ι → ℝ) (B' : ι → ι → ℝ),
      (∀ i, 0 ≤ q' i) ∧ (∑ i, q' i = r) ∧
      (∀ i, q i = 0 → q' i = 0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤ k+gridSize M r η ∧
      (∀ h, anchorResponse K D p q' h = anchorResponse K D p q h) ∧
      IsSkew B' ∧ (∀ i j, -M ≤ B' i j ∧ B' i j ≤ M) ∧
      (∀ a, response (blockMatrix K D B') (blockWeights p q') a ≤ η) := by
  classical
  obtain ⟨q', hq', hm', hs, hn, ha, hg, hc⟩ :=
    exact_game_sparse_cut_certificate k K D B p q M r η hM hr hη hp hq hmass hK hB hbound hresp
  obtain ⟨B', hsk', hb', hres'⟩ := completion_of_cuts_and_guards q' (score D p)
    M r η (le_of_lt hM) hq' hm' hc hg
  refine ⟨q', B', hq', hm', hs, hn, ha, hsk', hb', ?_⟩
  apply (block_response_bounds_iff K D B' p q' η).mpr
  refine ⟨?_, hres'⟩
  intro h
  rw [ha h]
  have hh := ((block_response_bounds_iff K D B p q 0).mp hresp).1 h
  linarith

end
end SparseCompletion
