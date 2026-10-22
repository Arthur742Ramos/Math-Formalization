/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import PaperWitness

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem nonnegative_mass_zero {ι : Type*} [Fintype ι] (q : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hm : ∑ i, q i=0) : q=fun _ => 0 := by
  classical
  funext i
  have hi := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => hq j) (Finset.mem_univ i)
  rw [hm] at hi
  exact le_antisymm hi (hq i)

theorem normalized_sparse_witness_all_mass {ι : Type*} [Fintype ι]
    (k : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ) (B : ι → ι → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r ρ η : ℝ)
    (hM : 0 < M) (hr : 0 ≤ r) (hη : 0 < η)
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
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤ min (Fintype.card ι) (k+1+gridSize M r η) ∧
      (Finset.univ.filter fun a => blockWeights p q' a ≠ 0).card ≤ min (k+Fintype.card ι) ((2 : ℕ)*k+1+gridSize M r η) ∧
      (∀ h, (∑ i, q' i*D i h) = ∑ i, q i*D i h) ∧
      IsSkew (blockMatrix K D B') ∧
      (∀ a b, -M ≤ blockMatrix K D B' a b ∧ blockMatrix K D B' a b ≤ M) ∧
      (∀ a, response (blockMatrix K D B') (blockWeights p q') a ≤ ρ+η) := by
  classical
  by_cases hz : r=0
  · have hzero : q=fun _ => 0 := nonnegative_mass_zero q hq (by simpa only [hz] using hqmass)
    have hc : (Finset.univ.filter fun i => q i ≠ 0).card=0 := by simp [hzero]
    have ha : (Finset.univ.filter fun h => p h ≠ 0).card ≤ k :=
      le_trans (Finset.card_filter_le _ _) (by simp)
    refine ⟨q,B,blockWeights_nonneg p q hp hq,?_,fun _ => rfl,fun _ hi => hi,?_,?_,
      fun _ => rfl,blockMatrix_skew K D B hK hB,blockMatrix_bounds K D B M hKb hDb hBb,?_⟩
    · rw [blockWeights_mass,hqmass]
      exact hpmass
    · rw [hc]
      exact Nat.zero_le _
    · rw [block_support_card,hc]
      omega
    · intro a
      exact le_trans (hresp a) (by linarith)
  · obtain ⟨q',B',hn,hm,ha,hs,hc,ht,hmo,hsk,hb,hrows⟩ :=
      normalized_sparse_witness k K D B p q M r ρ η hM (lt_of_le_of_ne hr (Ne.symm hz)) hη hp hq hpmass hqmass hK hB hKb hDb hBb hresp
    refine ⟨q',B',hn,hm,ha,hs,Nat.le_min.mpr ⟨?_,hc⟩,Nat.le_min.mpr ⟨?_,ht⟩,hmo,hsk,hb,hrows⟩
    · exact le_trans (Finset.card_filter_le _ _) (by simp)
    · exact le_trans (Finset.card_filter_le _ _) (by simp)

theorem normalized_exact_sparse_witness_all_mass {ι : Type*} [Fintype ι]
    (k : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ) (B : ι → ι → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r η : ℝ)
    (hM : 0 < M) (hr : 0 ≤ r) (hη : 0 < η)
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
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤ min (Fintype.card ι) (k+gridSize M r η) ∧
      (Finset.univ.filter fun a => blockWeights p q' a ≠ 0).card ≤ min (k+Fintype.card ι) ((2 : ℕ)*k+gridSize M r η) ∧
      (∀ h, (∑ i, q' i*D i h) = ∑ i, q i*D i h) ∧
      IsSkew (blockMatrix K D B') ∧
      (∀ a b, -M ≤ blockMatrix K D B' a b ∧ blockMatrix K D B' a b ≤ M) ∧
      (∀ a, response (blockMatrix K D B') (blockWeights p q') a ≤ η) := by
  classical
  by_cases hz : r=0
  · have hzero : q=fun _ => 0 := nonnegative_mass_zero q hq (by simpa only [hz] using hqmass)
    have hc : (Finset.univ.filter fun i => q i ≠ 0).card=0 := by simp [hzero]
    have ha : (Finset.univ.filter fun h => p h ≠ 0).card ≤ k :=
      le_trans (Finset.card_filter_le _ _) (by simp)
    refine ⟨q,B,blockWeights_nonneg p q hp hq,?_,fun _ => rfl,fun _ hi => hi,?_,?_,
      fun _ => rfl,blockMatrix_skew K D B hK hB,blockMatrix_bounds K D B M hKb hDb hBb,?_⟩
    · rw [blockWeights_mass,hqmass]
      exact hpmass
    · rw [hc]
      exact Nat.zero_le _
    · rw [block_support_card,hc]
      omega
    · intro a
      exact le_trans (hresp a) (by linarith)
  · obtain ⟨q',B',hn,hm,ha,hs,hc,ht,hmo,hsk,hb,hrows⟩ :=
      normalized_exact_sparse_witness k K D B p q M r η hM (lt_of_le_of_ne hr (Ne.symm hz)) hη hp hq hpmass hqmass hK hB hKb hDb hBb hresp
    refine ⟨q',B',hn,hm,ha,hs,Nat.le_min.mpr ⟨?_,hc⟩,Nat.le_min.mpr ⟨?_,ht⟩,hmo,hsk,hb,hrows⟩
    · exact le_trans (Finset.card_filter_le _ _) (by simp)
    · exact le_trans (Finset.card_filter_le _ _) (by simp)

end
end SparseCompletion
