/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import SparseCompletionWitness

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem block_support_card {α ι : Type*} [Fintype α] [Fintype ι]
    (p : α → ℝ) (q : ι → ℝ) :
    (Finset.univ.filter fun a => blockWeights p q a ≠ 0).card =
      (Finset.univ.filter fun h => p h ≠ 0).card+
      (Finset.univ.filter fun i => q i ≠ 0).card := by
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp only [Fintype.sum_sum_type, blockWeights, Sum.elim_inl, Sum.elim_inr]
  rfl

/-- Normalized, bounded whole-game specialization of the sparse witness.
    The conclusion preserves the prescribed anchor shares literally. -/
theorem normalized_sparse_witness {ι : Type*} [Fintype ι]
    (k : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ) (B : ι → ι → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r ρ η : ℝ)
    (hM : 0 < M) (hr : 0 < r) (hη : 0 < η)
    (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i)
    (hpmass : (∑ h, p h)+r = 1) (hqmass : ∑ i, q i = r)
    (hK : IsSkew K) (hB : IsSkew B)
    (hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M)
    (hDb : ∀ i h, -M ≤ D i h ∧ D i h ≤ M)
    (hBb : ∀ i j, -M ≤ B i j ∧ B i j ≤ M)
    (hresp : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ρ) :
    ∃ (q' : ι → ℝ) (B' : ι → ι → ℝ),
      (∀ a, 0 ≤ blockWeights p q' a) ∧ (∑ a, blockWeights p q' a) = 1 ∧
      (∀ h, blockWeights p q' (.inl h) = p h) ∧
      (∀ i, q i = 0 → q' i = 0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤ k+1+gridSize M r η ∧
      (Finset.univ.filter fun a => blockWeights p q' a ≠ 0).card ≤ (2 : ℕ)*k+1+gridSize M r η ∧
      (∀ h, (∑ i, q' i*D i h) = ∑ i, q i*D i h) ∧
      IsSkew (blockMatrix K D B') ∧
      (∀ a b, -M ≤ blockMatrix K D B' a b ∧ blockMatrix K D B' a b ≤ M) ∧
      (∀ a, response (blockMatrix K D B') (blockWeights p q') a ≤ ρ+η) := by
  classical
  obtain ⟨q', B', hn, hm, hs, hc, ha, hsk, hb, he⟩ :=
    game_sparse_completion k K D B p q M r ρ η hM hr hη hq hqmass hB
      (fun i j => (hBb i j).1) hresp
  refine ⟨q', B', blockWeights_nonneg p q' hp hn, ?_, fun _ => rfl, hs, hc, ?_, ?_,
    blockMatrix_skew K D B' hK hsk, blockMatrix_bounds K D B' M hKb hDb hb, he⟩
  · rw [blockWeights_mass, hm]
    exact hpmass
  · rw [block_support_card]
    have hanchor : (Finset.univ.filter fun h => p h ≠ 0).card ≤ k := by
      exact le_trans (Finset.card_filter_le _ _) (by simp)
    omega
  · intro h
    have hh := ha h
    unfold anchorResponse at hh
    have hsums : (∑ i, D i h*q' i) = ∑ i, D i h*q i := by linarith
    simpa only [mul_comm] using hsums
/-- Normalized, bounded whole-game specialization of the sparse witness.
    The conclusion preserves the prescribed anchor shares literally. -/
theorem normalized_exact_sparse_witness {ι : Type*} [Fintype ι]
    (k : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ) (B : ι → ι → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r η : ℝ)
    (hM : 0 < M) (hr : 0 < r) (hη : 0 < η)
    (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i)
    (hpmass : (∑ h, p h)+r = 1) (hqmass : ∑ i, q i = r)
    (hK : IsSkew K) (hB : IsSkew B)
    (hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M)
    (hDb : ∀ i h, -M ≤ D i h ∧ D i h ≤ M)
    (hBb : ∀ i j, -M ≤ B i j ∧ B i j ≤ M)
    (hresp : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ 0) :
    ∃ (q' : ι → ℝ) (B' : ι → ι → ℝ),
      (∀ a, 0 ≤ blockWeights p q' a) ∧ (∑ a, blockWeights p q' a) = 1 ∧
      (∀ h, blockWeights p q' (.inl h) = p h) ∧
      (∀ i, q i = 0 → q' i = 0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤ k+gridSize M r η ∧
      (Finset.univ.filter fun a => blockWeights p q' a ≠ 0).card ≤ (2 : ℕ)*k+gridSize M r η ∧
      (∀ h, (∑ i, q' i*D i h) = ∑ i, q i*D i h) ∧
      IsSkew (blockMatrix K D B') ∧
      (∀ a b, -M ≤ blockMatrix K D B' a b ∧ blockMatrix K D B' a b ≤ M) ∧
      (∀ a, response (blockMatrix K D B') (blockWeights p q') a ≤ η) := by
  classical
  obtain ⟨q', B', hn, hm, hs, hc, ha, hsk, hb, he⟩ :=
    exact_game_sparse_completion k K D B p q M r η hM hr hη hp hq hqmass hK hB hBb hresp
  refine ⟨q', B', blockWeights_nonneg p q' hp hn, ?_, fun _ => rfl, hs, hc, ?_, ?_,
    blockMatrix_skew K D B' hK hsk, blockMatrix_bounds K D B' M hKb hDb hb, he⟩
  · rw [blockWeights_mass, hm]
    exact hpmass
  · rw [block_support_card]
    have hanchor : (Finset.univ.filter fun h => p h ≠ 0).card ≤ k := by
      exact le_trans (Finset.card_filter_le _ _) (by simp)
    omega
  · intro h
    have hh := ha h
    unfold anchorResponse at hh
    have hsums : (∑ i, D i h*q' i) = ∑ i, D i h*q i := by linarith
    simpa only [mul_comm] using hsums

end
end SparseCompletion
