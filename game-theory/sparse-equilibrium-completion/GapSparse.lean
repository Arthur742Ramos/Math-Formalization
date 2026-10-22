/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import GapCertificates
public import GameSparseWitness
public import AllMassWitness

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

/-- Compression of a supplied finite-gap point preserves the original grid
    exactly. No second slack is introduced and no vertex algorithm is assumed. -/
theorem gap_sparse_point_positive {ι : Type*} [Fintype ι]
    (k : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r ρ η : ℝ) (hr : 0 < r)
    (h : fixedAnchorGapPoint K D p q M r ρ η) :
    ∃ q' : ι → ℝ, fixedAnchorGapPoint K D p q' M r ρ η ∧
      (∀ i, q i=0 → q' i=0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤
        min (Fintype.card ι) (k+1+gridSize M r η) ∧
      (∀ a, (∑ i, q' i*D i a)=∑ i, q i*D i a) ∧
      ∀ a, anchorResponse K D p q' a=anchorResponse K D p q a := by
  classical
  let H := gridSize M r η
  obtain ⟨q',hq',hm',hs,hc,hfeatures⟩ := finite_feature_compression (Fin k ⊕ Fin H)
    q (sparseFeatures k H D (fun i => score D p i-ρ) M r η) r h.1 h.2.1 hr
  have hmom : ∀ a, (∑ i, q' i*D i a)=∑ i, q i*D i a := fun a => hfeatures (.inl a)
  have hanchor := anchor_response_of_moments k K D p q q' hmom
  refine ⟨q',⟨hq',hm',h.2.2.1,?_,?_⟩,hs,?_,hmom,hanchor⟩
  · intro a
    rw [hanchor]
    exact h.2.2.2.1 a
  · intro l hl hlH
    let j : Fin H := ⟨l-1,by dsimp only [H]; omega⟩
    have hj : j.val+1=l := by dsimp only [j]; omega
    have he := hfeatures (.inr j)
    change (∑ i, q' i*max ((score D p i-ρ)-(M*r-gridNode M r η (j.val+1))) 0)=
      ∑ i, q i*max ((score D p i-ρ)-(M*r-gridNode M r η (j.val+1))) 0 at he
    rw [hj] at he
    change (∑ i, q' i*max ((score D p i-ρ)-(M*r-gridNode M r η l)) 0) ≤ _
    rw [he]
    exact h.2.2.2.2 l hl hlH
  · apply Nat.le_min.mpr
    constructor
    · exact le_trans (Finset.card_filter_le _ _) (by simp)
    · simpa only [Fintype.card_sum,Fintype.card_fin,Nat.add_right_comm k H 1,H] using hc

theorem gap_sparse_point {ι : Type*} [Fintype ι]
    (k : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r ρ η : ℝ)
    (h : fixedAnchorGapPoint K D p q M r ρ η) :
    ∃ q' : ι → ℝ, fixedAnchorGapPoint K D p q' M r ρ η ∧
      (∀ i, q i=0 → q' i=0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤
        min (Fintype.card ι) (k+1+gridSize M r η) ∧
      (∀ a, (∑ i, q' i*D i a)=∑ i, q i*D i a) ∧
      ∀ a, anchorResponse K D p q' a=anchorResponse K D p q a := by
  classical
  have hr : 0 ≤ r := by rw [←h.2.1]; exact Finset.sum_nonneg fun i _ => h.1 i
  by_cases hz : r=0
  · have hzero : q=fun _ => 0 := nonnegative_mass_zero q h.1 (by simpa only [hz] using h.2.1)
    refine ⟨q,h,fun _ hi => hi,?_,fun _ => rfl,fun _ => rfl⟩
    simp [hzero]
  · exact gap_sparse_point_positive k K D p q M r ρ η (lt_of_le_of_ne hr (Ne.symm hz)) h

theorem gap_sparse_completed_witness {ι : Type*} [Fintype ι]
    (k : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r ρ η : ℝ)
    (hM : 0 < M) (hη : 0 < η) (h : fixedAnchorGapPoint K D p q M r ρ η) :
    ∃ (q' : ι → ℝ) (B' : ι → ι → ℝ),
      (∀ i, 0 ≤ q' i) ∧ (∑ i, q' i)=r ∧
      (∀ i, q i=0 → q' i=0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤
        min (Fintype.card ι) (k+1+gridSize M r η) ∧
      (∀ a, (∑ i, q' i*D i a)=∑ i, q i*D i a) ∧
      (∀ a, anchorResponse K D p q' a=anchorResponse K D p q a) ∧
      IsSkew B' ∧ (∀ i j, -M ≤ B' i j ∧ B' i j ≤ M) ∧
      ∀ a, response (blockMatrix K D B') (blockWeights p q') a ≤ ρ+η := by
  obtain ⟨q',hg,hs,hc,hm,hanchor⟩ := gap_sparse_point k K D p q M r ρ η h
  have hr : 0 ≤ r := by rw [←h.2.1]; exact Finset.sum_nonneg fun i _ => h.1 i
  obtain ⟨B',hB,hb,hrows⟩ := gap_point_completed_witness K D p q' M r ρ η hM hr hη hg
  exact ⟨q',B',hg.1,hg.2.1,hs,hc,hm,hanchor,hB,hb,hrows⟩

/-- Full normalized-game sparse gap witness, still at the original single slack. -/
theorem normalized_gap_sparse_completed_witness {ι : Type*} [Fintype ι]
    (k : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r ρ η : ℝ)
    (hM : 0 < M) (hη : 0 < η) (hp : ∀ a, 0 ≤ p a)
    (hnorm : (∑ a, p a)+r=1) (hK : IsSkew K)
    (hKb : ∀ a b, -M ≤ K a b ∧ K a b ≤ M)
    (hDb : ∀ i a, -M ≤ D i a ∧ D i a ≤ M)
    (h : fixedAnchorGapPoint K D p q M r ρ η) :
    ∃ (q' : ι → ℝ) (B' : ι → ι → ℝ),
      (∀ a, 0 ≤ blockWeights p q' a) ∧ (∑ a, blockWeights p q' a)=1 ∧
      (∀ i, q i=0 → q' i=0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤
        min (Fintype.card ι) (k+1+gridSize M r η) ∧
      (Finset.univ.filter fun a => blockWeights p q' a ≠ 0).card ≤
        min (k+Fintype.card ι) ((2 : ℕ)*k+1+gridSize M r η) ∧
      (∀ a, (∑ i, q' i*D i a)=∑ i, q i*D i a) ∧
      (∀ a, anchorResponse K D p q' a=anchorResponse K D p q a) ∧
      IsSkew (blockMatrix K D B') ∧
      (∀ a b, -M ≤ blockMatrix K D B' a b ∧ blockMatrix K D B' a b ≤ M) ∧
      ∀ a, response (blockMatrix K D B') (blockWeights p q') a ≤ ρ+η := by
  classical
  obtain ⟨q',B',hq',hm,hs,hc,hmo,ha,hB,hb,hrows⟩ :=
    gap_sparse_completed_witness k K D p q M r ρ η hM hη h
  refine ⟨q',B',blockWeights_nonneg p q' hp hq',?_,hs,hc,?_,hmo,ha,
    blockMatrix_skew K D B' hK hB,blockMatrix_bounds K D B' M hKb hDb hb,hrows⟩
  · rw [blockWeights_mass,hm]
    exact hnorm
  · rw [block_support_card]
    have hpa : (Finset.univ.filter fun a => p a ≠ 0).card ≤ k :=
      le_trans (Finset.card_filter_le _ _) (by simp)
    have h1 := le_trans hc (min_le_left _ _)
    have h2 := le_trans hc (min_le_right _ _)
    exact Nat.le_min.mpr ⟨by omega,by omega⟩

end
end SparseCompletion
