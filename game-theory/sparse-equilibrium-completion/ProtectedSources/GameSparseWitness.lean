/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.SparseWitness
public import ProtectedSources.GameModel

@[expose] public section

open scoped BigOperators

namespace SparseCompletion
noncomputable section

theorem anchor_response_of_moments {ι : Type*} [Fintype ι]
    (k : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ)
    (p : Fin k → ℝ) (q q' : ι → ℝ)
    (hm : ∀ h, (∑ i, q' i*D i h) = ∑ i, q i*D i h) :
    ∀ h, anchorResponse K D p q' h = anchorResponse K D p q h := by
  intro h
  unfold anchorResponse
  congr 1
  simpa only [mul_comm] using hm h

/-- Original-game sparsification through all scalar completion conditions,
    including omitted-row guards. SparseCompletionWitness combines these
    conditions with the weighted completion sufficiency theorem. -/
theorem game_sparse_cut_certificate {ι : Type*} [Fintype ι]
    (k : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ) (B : ι → ι → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r ρ η : ℝ)
    (hM : 0 < M) (hr : 0 < r) (hη : 0 < η)
    (hq : ∀ i, 0 ≤ q i) (hmass : ∑ i, q i = r)
    (hB : IsSkew B) (hbound : ∀ i j, -M ≤ B i j)
    (hresp : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ρ) :
    ∃ q' : ι → ℝ, (∀ i, 0 ≤ q' i) ∧ (∑ i, q' i = r) ∧
      (∀ i, q i = 0 → q' i = 0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤ k+1+gridSize M r η ∧
      (∀ h, anchorResponse K D p q' h = anchorResponse K D p q h) ∧
      (∀ i, score D p i ≤ (ρ+η)+M*r) ∧
      Cuts M r q' (fun i => score D p i-(ρ+η)) := by
  classical
  have hres := ((block_response_bounds_iff K D B p q ρ).mp hresp).2
  have hcuts := completion_cuts_necessary q (score D p) B M r ρ hq hmass hB hbound hres
  obtain ⟨q', hq', hmass', hsupp, hcard, hfeatures, hc⟩ :=
    canonical_sparse_cut_witness k D q (fun i => score D p i-ρ) M r η hM hr hη hq hmass hcuts
  refine ⟨q', hq', hmass', hsupp, hcard, anchor_response_of_moments k K D p q q' hfeatures, ?_, ?_⟩
  · intro i
    have hg := response_guard q (score D p) B M r ρ hq hmass hbound hres i
    linarith
  · convert hc using 1
    funext i
    ring

theorem exact_game_sparse_cut_certificate {ι : Type*} [Fintype ι]
    (k : ℕ) (K : Fin k → Fin k → ℝ) (D : ι → Fin k → ℝ) (B : ι → ι → ℝ)
    (p : Fin k → ℝ) (q : ι → ℝ) (M r η : ℝ)
    (hM : 0 < M) (hr : 0 < r) (hη : 0 < η)
    (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i) (hmass : ∑ i, q i = r)
    (hK : IsSkew K) (hB : IsSkew B) (hbound : ∀ i j, -M ≤ B i j ∧ B i j ≤ M)
    (hresp : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ 0) :
    ∃ q' : ι → ℝ, (∀ i, 0 ≤ q' i) ∧ (∑ i, q' i = r) ∧
      (∀ i, q i = 0 → q' i = 0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤ k+gridSize M r η ∧
      (∀ h, anchorResponse K D p q' h = anchorResponse K D p q h) ∧
      (∀ i, score D p i ≤ η+M*r) ∧
      Cuts M r q' (fun i => score D p i-η) := by
  classical
  have hres := ((block_response_bounds_iff K D B p q 0).mp hresp).2
  have hcuts0 := completion_cuts_necessary q (score D p) B M r 0 hq hmass hB
    (fun i j => (hbound i j).1) hres
  have hcuts : Cuts M r q (score D p) := by simpa only [sub_zero] using hcuts0
  have hmean := exact_score_mean_zero K D B p q hp hq hK hB hresp
  have hlow : ∀ i, q i ≠ 0 → -M*r ≤ score D p i := by
    intro i hi
    simpa only [neg_mul] using
      (abs_le.mp (exact_score_bounds K D B p q M r hp hq hmass hK hB hbound hresp i hi)).1
  obtain ⟨q', hq', hmass', hsupp, hcard, hfeatures, hc⟩ :=
    exact_sparse_cut_witness k (gridSize M r η) D p q (score D p) M r η hM hr hη
      (gridSize_bound M r η hM (le_of_lt hr) hη) hq hmass hcuts (fun _ => rfl) hmean hlow
  refine ⟨q', hq', hmass', hsupp, hcard, anchor_response_of_moments k K D p q q' hfeatures, ?_, hc⟩
  intro i
  have hg := response_guard q (score D p) B M r 0 hq hmass
    (fun i j => (hbound i j).1) hres i
  linarith

end
end SparseCompletion
