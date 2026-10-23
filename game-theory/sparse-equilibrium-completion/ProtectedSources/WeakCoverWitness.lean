/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.WeakCover

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem normalized_weak_cover_witness {ι : Type*} [Fintype ι]
    (k d : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ) (F : ι → Fin d → ℝ) (B : ι → ι → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r ρ η β : ℝ)
    (hM : 0 < M) (hr : 0 ≤ r) (hη : 0 < η)
    (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i)
    (hpmass : (∑ h, p h)+r = 1) (hqmass : ∑ i, q i = r)
    (hK : IsSkew K) (hB : IsSkew B)
    (hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M)
    (hDb : ∀ i h, -M ≤ D i h ∧ D i h ≤ M)
    (hBb : ∀ i j, -M ≤ B i j ∧ B i j ≤ M)
    (hresp : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ρ)
    (lo hi : (Fin k ⊕ ι) → (Fin k ⊕ ι) → ℝ)
    (hβ : 0 ≤ β)
    (hlu : ∀ i j, i ≠ j → lo (.inr i) (.inr j) ≤ hi (.inr i) (.inr j))
    (hlo : ∀ i j, i ≠ j → -M ≤ lo (.inr i) (.inr j))
    (hhi : ∀ i j, i ≠ j → hi (.inr i) (.inr j) ≤ M)
    (hrev : ∀ i j, i ≠ j → lo (.inr i) (.inr j)= -hi (.inr j) (.inr i) ∧
      hi (.inr i) (.inr j)= -lo (.inr j) (.inr i))
    (hloss : ∀ i j, i ≠ j → intervalLoss M (lo (.inr i) (.inr j)) (hi (.inr i) (.inr j)) ≤ β)
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
      (∀ a, response (blockMatrix K D B') (blockWeights p q') a ≤ ρ+η+β*r) ∧
      offDiagonalIntervals lo hi (blockMatrix K D B') ∧
      (∀ a b, ((∃ h, a=Sum.inl h) ∨ ∃ h, b=Sum.inl h) →
        blockMatrix K D B' a b=blockMatrix K D B a b) ∧
      ∀ h, response (blockMatrix K D B') (blockWeights p q') (.inl h)=
        response (blockMatrix K D B) (blockWeights p q) (.inl h) := by
  obtain ⟨q',B',hn,hm,ha,hs,hc,ht,hD,hF,hsk,hb,hrows⟩ :=
    normalized_sparse_witness_extra_moments_all_mass k d K D F B p q M r ρ η hM hr hη hp hq hpmass hqmass hK hB hKb hDb hBb hresp
  let loR := fun i j => lo (Sum.inr i) (Sum.inr j)
  let hiR := fun i j => hi (Sum.inr i) (Sum.inr j)
  let C := projectedResidual loR hiR B'
  have hB' : IsSkew B' := fun i j => hsk (.inr i) (.inr j)
  have hb' : ∀ i j, -M ≤ B' i j ∧ B' i j ≤ M := fun i j => hb (.inr i) (.inr j)
  have hq'n : ∀ i, 0 ≤ q' i := fun i => hn (.inr i)
  have hq'm : ∑ i, q' i=r := by
    have hmass := blockWeights_mass p q'
    rw [hm] at hmass
    linarith
  have hC : IsSkew C := projected_residual_skew loR hiR B' hB' hlu hrev
  have hCb : ∀ i j, -M ≤ C i j ∧ C i j ≤ M :=
    projected_residual_bounds loR hiR B' M (le_of_lt hM) hlu hlo hhi
  have hCrows := residual_projection_response_bound K D B' loR hiR p q' M β r (ρ+η)
    hβ hq'n hq'm hB' hb' hlu hlo hloss hrows
  refine ⟨q',C,hn,hm,ha,hs,hc,ht,hD,hF,blockMatrix_skew K D C hK hC,
    blockMatrix_bounds K D C M hKb hDb hCb,hCrows,?_,?_,?_⟩
  · exact projected_block_intervals K D B B' lo hi hI hlu
  · intro a b hab
    exact anchor_incident_entries_preserved K D B C a b hab
  · intro h
    rw [block_response_anchor,block_response_anchor]
    exact anchor_response_of_moments k K D p q q' hD h

theorem normalized_exact_weak_cover_witness {ι : Type*} [Fintype ι]
    (k d : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ) (F : ι → Fin d → ℝ) (B : ι → ι → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r η β : ℝ)
    (hM : 0 < M) (hr : 0 ≤ r) (hη : 0 < η)
    (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i)
    (hpmass : (∑ h, p h)+r = 1) (hqmass : ∑ i, q i = r)
    (hK : IsSkew K) (hB : IsSkew B)
    (hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M)
    (hDb : ∀ i h, -M ≤ D i h ∧ D i h ≤ M)
    (hBb : ∀ i j, -M ≤ B i j ∧ B i j ≤ M)
    (hresp : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ 0)
    (lo hi : (Fin k ⊕ ι) → (Fin k ⊕ ι) → ℝ)
    (hβ : 0 ≤ β)
    (hlu : ∀ i j, i ≠ j → lo (.inr i) (.inr j) ≤ hi (.inr i) (.inr j))
    (hlo : ∀ i j, i ≠ j → -M ≤ lo (.inr i) (.inr j))
    (hhi : ∀ i j, i ≠ j → hi (.inr i) (.inr j) ≤ M)
    (hrev : ∀ i j, i ≠ j → lo (.inr i) (.inr j)= -hi (.inr j) (.inr i) ∧
      hi (.inr i) (.inr j)= -lo (.inr j) (.inr i))
    (hloss : ∀ i j, i ≠ j → intervalLoss M (lo (.inr i) (.inr j)) (hi (.inr i) (.inr j)) ≤ β)
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
      (∀ a, response (blockMatrix K D B') (blockWeights p q') a ≤ η+β*r) ∧
      offDiagonalIntervals lo hi (blockMatrix K D B') ∧
      (∀ a b, ((∃ h, a=Sum.inl h) ∨ ∃ h, b=Sum.inl h) →
        blockMatrix K D B' a b=blockMatrix K D B a b) ∧
      ∀ h, response (blockMatrix K D B') (blockWeights p q') (.inl h)=
        response (blockMatrix K D B) (blockWeights p q) (.inl h) := by
  obtain ⟨q',B',hn,hm,ha,hs,hc,ht,hD,hF,hsk,hb,hrows⟩ :=
    normalized_exact_sparse_witness_extra_moments_all_mass k d K D F B p q M r η hM hr hη hp hq hpmass hqmass hK hB hKb hDb hBb hresp
  let loR := fun i j => lo (Sum.inr i) (Sum.inr j)
  let hiR := fun i j => hi (Sum.inr i) (Sum.inr j)
  let C := projectedResidual loR hiR B'
  have hB' : IsSkew B' := fun i j => hsk (.inr i) (.inr j)
  have hb' : ∀ i j, -M ≤ B' i j ∧ B' i j ≤ M := fun i j => hb (.inr i) (.inr j)
  have hq'n : ∀ i, 0 ≤ q' i := fun i => hn (.inr i)
  have hq'm : ∑ i, q' i=r := by
    have hmass := blockWeights_mass p q'
    rw [hm] at hmass
    linarith
  have hC : IsSkew C := projected_residual_skew loR hiR B' hB' hlu hrev
  have hCb : ∀ i j, -M ≤ C i j ∧ C i j ≤ M :=
    projected_residual_bounds loR hiR B' M (le_of_lt hM) hlu hlo hhi
  have hCrows := residual_projection_response_bound K D B' loR hiR p q' M β r η
    hβ hq'n hq'm hB' hb' hlu hlo hloss hrows
  refine ⟨q',C,hn,hm,ha,hs,hc,ht,hD,hF,blockMatrix_skew K D C hK hC,
    blockMatrix_bounds K D C M hKb hDb hCb,hCrows,?_,?_,?_⟩
  · exact projected_block_intervals K D B B' lo hi hI hlu
  · intro a b hab
    exact anchor_incident_entries_preserved K D B C a b hab
  · intro h
    rw [block_response_anchor,block_response_anchor]
    exact anchor_response_of_moments k K D p q q' hD h

end
end SparseCompletion
