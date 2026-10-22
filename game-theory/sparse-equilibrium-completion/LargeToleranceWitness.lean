/- AI-assisted formalization under the repository Apache-2.0 license.
The no-grid large-tolerance refinement in the source sparsification section. -/
module
public import ExtraMomentWitness

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

/-- When η covers the entire possible residual response, zero residual payoffs
suffice after preserving the anchor and extra moments. No call nodes remain. -/
theorem large_tolerance_sparse_moments {ι : Type*} [Fintype ι]
    (k d : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ)
    (F : ι → Fin d → ℝ) (B : ι → ι → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r ρ η : ℝ)
    (hM : 0 ≤ M) (hr : 0 < r) (hη : M*r ≤ η)
    (hq : ∀ i, 0 ≤ q i) (hmass : ∑ i, q i = r)
    (hbound : ∀ i j, -M ≤ B i j)
    (hresp : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ρ) :
    ∃ q' : ι → ℝ, (∀ i, 0 ≤ q' i) ∧ (∑ i, q' i = r) ∧
      (∀ i, q i = 0 → q' i = 0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤ k+d+1 ∧
      (∀ h, (∑ i, q' i*D i h) = ∑ i, q i*D i h) ∧
      (∀ g, (∑ i, q' i*F i g) = ∑ i, q i*F i g) ∧
      (∀ a, response (blockMatrix K D (fun _ _ => 0)) (blockWeights p q') a ≤ ρ+η) := by
  classical
  let G : ι → (Fin k ⊕ Fin d) → ℝ := fun i => Sum.elim (D i) (F i)
  obtain ⟨q', hn, hm, hs, hc, hf⟩ :=
    finite_feature_compression (Fin k ⊕ Fin d) q G r hq hmass hr
  have hd : ∀ h, (∑ i, q' i*D i h) = ∑ i, q i*D i h := by
    intro h
    exact hf (.inl h)
  have he : ∀ g, (∑ i, q' i*F i g) = ∑ i, q i*F i g := by
    intro g
    exact hf (.inr g)
  refine ⟨q', hn, hm, hs, ?_, hd, he, ?_⟩
  · simpa only [Fintype.card_sum, Fintype.card_fin] using hc
  · have hb := (block_response_bounds_iff K D B p q ρ).mp hresp
    have hg := response_guard q (score D p) B M r ρ hq hmass hbound hb.2
    have hη0 : 0 ≤ η := le_trans (mul_nonneg hM (le_of_lt hr)) hη
    apply (block_response_bounds_iff K D (fun _ _ => 0) p q' (ρ+η)).mpr
    constructor
    · intro h
      rw [anchor_response_of_moments k K D p q q' hd]
      exact le_trans (hb.1 h) (le_add_of_nonneg_right hη0)
    · intro i
      simpa only [response, zero_mul, Finset.sum_const_zero, add_zero] using
        (show score D p i ≤ ρ+η by linarith [hg i])

/-- The optional source refinement, with no additional moment constraints. -/
theorem large_tolerance_sparse_witness {ι : Type*} [Fintype ι]
    (k : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ) (B : ι → ι → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r ρ η : ℝ)
    (hM : 0 ≤ M) (hr : 0 < r) (hη : M*r ≤ η)
    (hq : ∀ i, 0 ≤ q i) (hmass : ∑ i, q i = r)
    (hbound : ∀ i j, -M ≤ B i j)
    (hresp : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ρ) :
    ∃ q' : ι → ℝ, (∀ i, 0 ≤ q' i) ∧ (∑ i, q' i = r) ∧
      (∀ i, q i = 0 → q' i = 0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤ k+1 ∧
      (∀ h, (∑ i, q' i*D i h) = ∑ i, q i*D i h) ∧
      (∀ a, response (blockMatrix K D (fun _ _ => 0)) (blockWeights p q') a ≤ ρ+η) := by
  obtain ⟨q', hn, hm, hs, hc, hd, _, he⟩ :=
    large_tolerance_sparse_moments k 0 K D (fun _ g => Fin.elim0 g) B p q M r ρ η
      hM hr hη hq hmass hbound hresp
  exact ⟨q', hn, hm, hs, by simpa only [Nat.add_zero] using hc, hd, he⟩

/-- Whole-game version: retain the anchor shares, all extra moments, and at
most 2k+d+1 total support points, with the explicit zero residual block. -/
theorem normalized_large_tolerance_sparse_moments {ι : Type*} [Fintype ι]
    (k d : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ)
    (F : ι → Fin d → ℝ) (B : ι → ι → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r ρ η : ℝ)
    (hM : 0 ≤ M) (hr : 0 < r) (hη : M*r ≤ η)
    (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i)
    (hpmass : (∑ h, p h)+r=1) (hmass : ∑ i, q i=r)
    (hK : IsSkew K)
    (hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M)
    (hDb : ∀ i h, -M ≤ D i h ∧ D i h ≤ M)
    (hbound : ∀ i j, -M ≤ B i j)
    (hresp : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ρ) :
    ∃ q' : ι → ℝ,
      (∀ a, 0 ≤ blockWeights p q' a) ∧ (∑ a, blockWeights p q' a)=1 ∧
      (∀ h, blockWeights p q' (.inl h)=p h) ∧
      (∀ i, q i=0 → q' i=0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤ k+d+1 ∧
      (Finset.univ.filter fun a => blockWeights p q' a ≠ 0).card ≤ 2*k+d+1 ∧
      (∀ h, (∑ i, q' i*D i h)=∑ i, q i*D i h) ∧
      (∀ g, (∑ i, q' i*F i g)=∑ i, q i*F i g) ∧
      IsSkew (blockMatrix K D (fun _ _ => 0)) ∧
      (∀ a b, -M ≤ blockMatrix K D (fun _ _ => 0) a b ∧
        blockMatrix K D (fun _ _ => 0) a b ≤ M) ∧
      (∀ a, response (blockMatrix K D (fun _ _ => 0)) (blockWeights p q') a ≤ ρ+η) := by
  classical
  obtain ⟨q', hn, hm, hs, hc, hd, he, hb⟩ :=
    large_tolerance_sparse_moments k d K D F B p q M r ρ η hM hr hη hq hmass hbound hresp
  refine ⟨q', blockWeights_nonneg p q' hp hn, ?_, fun _ => rfl, hs, hc, ?_, hd, he,
    blockMatrix_skew K D _ hK (by intro i j; simp only [neg_zero]),
    blockMatrix_bounds K D _ M hKb hDb (fun _ _ => ⟨by linarith, hM⟩), hb⟩
  · rw [blockWeights_mass, hm]
    exact hpmass
  · rw [block_support_card]
    have ha : (Finset.univ.filter fun h => p h ≠ 0).card ≤ k :=
      le_trans (Finset.card_filter_le _ _) (by simp only [Finset.card_univ, Fintype.card_fin]; exact le_rfl)
    omega

end
end SparseCompletion
