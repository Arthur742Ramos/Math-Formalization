/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import GapSparse
public import IntervalGap

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

/-- Recover compatible cross data once and hold it fixed during compression. -/
theorem interval_gap_sparse_completed_witness {ι : Type*} [Fintype ι]
    (k : ℕ) (K : Fin k → Fin k → ℝ) (lo hi V : ι → Fin k → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r ρ η : ℝ)
    (hM : 0 < M) (hη : 0 < η) (hlu : ∀ i a, lo i a ≤ hi i a)
    (h : intervalGapPoint K lo hi V p q M r ρ η) :
    ∃ (q' : ι → ℝ) (B' : ι → ι → ℝ),
      (∀ i a, lo i a ≤ intervalCrossRecover lo V q i a ∧
        intervalCrossRecover lo V q i a ≤ hi i a) ∧
      (∀ i, 0 ≤ q' i) ∧ (∑ i, q' i)=r ∧
      (∀ i, q i=0 → q' i=0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤
        min (Fintype.card ι) (k+1+gridSize M r η) ∧
      (∀ a, (∑ i, q' i*intervalCrossRecover lo V q i a)=
        ∑ i, q i*intervalCrossRecover lo V q i a) ∧
      (∀ a, anchorResponse K (intervalCrossRecover lo V q) p q' a=
        anchorResponse K (intervalCrossRecover lo V q) p q a) ∧
      IsSkew B' ∧ (∀ i j, -M ≤ B' i j ∧ B' i j ≤ M) ∧
      ∀ a, response (blockMatrix K (intervalCrossRecover lo V q) B')
        (blockWeights p q') a ≤ ρ+η := by
  obtain ⟨hD,hg⟩ := interval_gap_recovered_exact_point K lo hi V p q M r ρ η hlu h
  obtain ⟨q',B',hq',hm,hs,hc,hmo,ha,hB,hb,hrows⟩ :=
    gap_sparse_completed_witness k K (intervalCrossRecover lo V q) p q M r ρ η hM hη hg
  exact ⟨q',B',hD,hq',hm,hs,hc,hmo,ha,hB,hb,hrows⟩

theorem normalized_interval_gap_sparse_completed_witness {ι : Type*} [Fintype ι]
    (k : ℕ) (K : Fin k → Fin k → ℝ) (lo hi V : ι → Fin k → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r ρ η : ℝ)
    (hM : 0 < M) (hη : 0 < η) (hp : ∀ a, 0 ≤ p a)
    (hnorm : (∑ a, p a)+r=1) (hK : IsSkew K)
    (hKb : ∀ a b, -M ≤ K a b ∧ K a b ≤ M)
    (hlo : ∀ i a, -M ≤ lo i a) (hhi : ∀ i a, hi i a ≤ M)
    (hlu : ∀ i a, lo i a ≤ hi i a)
    (h : intervalGapPoint K lo hi V p q M r ρ η) :
    ∃ (q' : ι → ℝ) (B' : ι → ι → ℝ),
      (∀ i a, lo i a ≤ intervalCrossRecover lo V q i a ∧
        intervalCrossRecover lo V q i a ≤ hi i a) ∧
      (∀ a, 0 ≤ blockWeights p q' a) ∧ (∑ a, blockWeights p q' a)=1 ∧
      (∀ i, q i=0 → q' i=0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤
        min (Fintype.card ι) (k+1+gridSize M r η) ∧
      (Finset.univ.filter fun a => blockWeights p q' a ≠ 0).card ≤
        min (k+Fintype.card ι) ((2 : ℕ)*k+1+gridSize M r η) ∧
      (∀ a, (∑ i, q' i*intervalCrossRecover lo V q i a)=
        ∑ i, q i*intervalCrossRecover lo V q i a) ∧
      (∀ a, anchorResponse K (intervalCrossRecover lo V q) p q' a=
        anchorResponse K (intervalCrossRecover lo V q) p q a) ∧
      IsSkew (blockMatrix K (intervalCrossRecover lo V q) B') ∧
      (∀ a b, -M ≤ blockMatrix K (intervalCrossRecover lo V q) B' a b ∧
        blockMatrix K (intervalCrossRecover lo V q) B' a b ≤ M) ∧
      ∀ a, response (blockMatrix K (intervalCrossRecover lo V q) B')
        (blockWeights p q') a ≤ ρ+η := by
  obtain ⟨hD,hg⟩ := interval_gap_recovered_exact_point K lo hi V p q M r ρ η hlu h
  have hDb : ∀ i a, -M ≤ intervalCrossRecover lo V q i a ∧ intervalCrossRecover lo V q i a ≤ M :=
    fun i a => ⟨le_trans (hlo i a) (hD i a).1,le_trans (hD i a).2 (hhi i a)⟩
  obtain ⟨q',B',hn,hm,hs,hc,ht,hmo,ha,hB,hb,hrows⟩ :=
    normalized_gap_sparse_completed_witness k K (intervalCrossRecover lo V q) p q M r ρ η
      hM hη hp hnorm hK hKb hDb hg
  exact ⟨q',B',hD,hn,hm,hs,hc,ht,hmo,ha,hB,hb,hrows⟩

end
end SparseCompletion
