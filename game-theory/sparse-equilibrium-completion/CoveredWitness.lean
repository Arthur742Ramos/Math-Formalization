/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ObservationCover

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem normalized_cover_witness {ι : Type*} [Fintype ι]
    (k d : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ) (F : ι → Fin d → ℝ) (B : ι → ι → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r ρ η : ℝ)
    (hM : 0 < M) (hr : 0 ≤ r) (hη : 0 < η)
    (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i)
    (hpmass : (∑ h, p h)+r = 1) (hqmass : ∑ i, q i = r)
    (hK : IsSkew K) (hB : IsSkew B)
    (hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M)
    (hDb : ∀ i h, -M ≤ D i h ∧ D i h ≤ M)
    (hBb : ∀ i j, -M ≤ B i j ∧ B i j ≤ M)
    (hresp : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ρ)
    (lo hi : (Fin k ⊕ ι) → (Fin k ⊕ ι) → ℝ)
    (hcover : freeResidualIntervals lo hi M)
    (hI : offDiagonalIntervals lo hi (blockMatrix K D B)) :
    ∃ (q' : ι → ℝ) (B' : ι → ι → ℝ),
      (∀ a, 0 ≤ blockWeights p q' a) ∧ (∑ a, blockWeights p q' a) = 1 ∧
      (∀ h, blockWeights p q' (.inl h) = p h) ∧
      (∀ i, q i = 0 → q' i = 0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤ min (Fintype.card ι) (k+d+1+gridSize M r η) ∧
      (Finset.univ.filter fun a => blockWeights p q' a ≠ 0).card ≤ min (k+Fintype.card ι) ((2 : ℕ)*k+d+1+gridSize M r η) ∧
      (∀ h, (∑ i, q' i*D i h) = ∑ i, q i*D i h) ∧
      (∀ g, (∑ i, q' i*F i g) = ∑ i, q i*F i g) ∧
      IsSkew (blockMatrix K D B') ∧
      (∀ a b, -M ≤ blockMatrix K D B' a b ∧ blockMatrix K D B' a b ≤ M) ∧
      (∀ a, response (blockMatrix K D B') (blockWeights p q') a ≤ ρ+η) ∧
      offDiagonalIntervals lo hi (blockMatrix K D B') ∧
      (∀ a b, ((∃ h, a=Sum.inl h) ∨ ∃ h, b=Sum.inl h) →
        blockMatrix K D B' a b=blockMatrix K D B a b) ∧
      ∀ h, response (blockMatrix K D B') (blockWeights p q') (.inl h)=
        response (blockMatrix K D B) (blockWeights p q) (.inl h) := by
  obtain ⟨q',B',hn,hm,ha,hs,hc,ht,hD,hF,hsk,hb,hrows⟩ :=
    normalized_sparse_witness_extra_moments_all_mass k d K D F B p q M r ρ η hM hr hη hp hq hpmass hqmass hK hB hKb hDb hBb hresp
  refine ⟨q',B',hn,hm,ha,hs,hc,ht,hD,hF,hsk,hb,hrows,?_,?_,?_⟩
  · exact cover_intervals_preserved K D B B' lo hi M hcover hI (fun i j => hb (.inr i) (.inr j))
  · intro a b hab
    exact anchor_incident_entries_preserved K D B B' a b hab
  · intro h
    rw [block_response_anchor,block_response_anchor]
    exact anchor_response_of_moments k K D p q q' hD h

theorem normalized_exact_cover_witness {ι : Type*} [Fintype ι]
    (k d : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ) (F : ι → Fin d → ℝ) (B : ι → ι → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r η : ℝ)
    (hM : 0 < M) (hr : 0 ≤ r) (hη : 0 < η)
    (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i)
    (hpmass : (∑ h, p h)+r = 1) (hqmass : ∑ i, q i = r)
    (hK : IsSkew K) (hB : IsSkew B)
    (hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M)
    (hDb : ∀ i h, -M ≤ D i h ∧ D i h ≤ M)
    (hBb : ∀ i j, -M ≤ B i j ∧ B i j ≤ M)
    (hresp : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ 0)
    (lo hi : (Fin k ⊕ ι) → (Fin k ⊕ ι) → ℝ)
    (hcover : freeResidualIntervals lo hi M)
    (hI : offDiagonalIntervals lo hi (blockMatrix K D B)) :
    ∃ (q' : ι → ℝ) (B' : ι → ι → ℝ),
      (∀ a, 0 ≤ blockWeights p q' a) ∧ (∑ a, blockWeights p q' a) = 1 ∧
      (∀ h, blockWeights p q' (.inl h) = p h) ∧
      (∀ i, q i = 0 → q' i = 0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤ min (Fintype.card ι) (k+d+gridSize M r η) ∧
      (Finset.univ.filter fun a => blockWeights p q' a ≠ 0).card ≤ min (k+Fintype.card ι) ((2 : ℕ)*k+d+gridSize M r η) ∧
      (∀ h, (∑ i, q' i*D i h) = ∑ i, q i*D i h) ∧
      (∀ g, (∑ i, q' i*F i g) = ∑ i, q i*F i g) ∧
      IsSkew (blockMatrix K D B') ∧
      (∀ a b, -M ≤ blockMatrix K D B' a b ∧ blockMatrix K D B' a b ≤ M) ∧
      (∀ a, response (blockMatrix K D B') (blockWeights p q') a ≤ η) ∧
      offDiagonalIntervals lo hi (blockMatrix K D B') ∧
      (∀ a b, ((∃ h, a=Sum.inl h) ∨ ∃ h, b=Sum.inl h) →
        blockMatrix K D B' a b=blockMatrix K D B a b) ∧
      ∀ h, response (blockMatrix K D B') (blockWeights p q') (.inl h)=
        response (blockMatrix K D B) (blockWeights p q) (.inl h) := by
  obtain ⟨q',B',hn,hm,ha,hs,hc,ht,hD,hF,hsk,hb,hrows⟩ :=
    normalized_exact_sparse_witness_extra_moments_all_mass k d K D F B p q M r η hM hr hη hp hq hpmass hqmass hK hB hKb hDb hBb hresp
  refine ⟨q',B',hn,hm,ha,hs,hc,ht,hD,hF,hsk,hb,hrows,?_,?_,?_⟩
  · exact cover_intervals_preserved K D B B' lo hi M hcover hI (fun i j => hb (.inr i) (.inr j))
  · intro a b hab
    exact anchor_incident_entries_preserved K D B B' a b hab
  · intro h
    rw [block_response_anchor,block_response_anchor]
    exact anchor_response_of_moments k K D p q q' hD h

end
end SparseCompletion
