/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import SparseWitness

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def extraSparseFeatures {ι : Type*} (k d H : ℕ) (D : ι → Fin k → ℝ)
    (F : ι → Fin d → ℝ) (v : ι → ℝ) (M r η : ℝ) (i : ι) :
    ((Fin k ⊕ Fin d) ⊕ Fin H) → ℝ :=
  Sum.elim (Sum.elim (D i) (F i))
    (fun l => max (v i-(M*r-gridNode M r η (l.val+1))) 0)

theorem sparse_cut_witness_extra_moments {ι : Type*} [Fintype ι]
    (k d H : ℕ) (D : ι → Fin k → ℝ) (F : ι → Fin d → ℝ) (q v : ι → ℝ) (M r η : ℝ)
    (hM : 0 < M) (hr : 0 < r) (hη : 0 < η)
    (hH : M*r ≤ η*(H:ℝ)^2) (hq : ∀ i, 0 ≤ q i)
    (hmass : ∑ i, q i = r) (hcuts : Cuts M r q v) :
    ∃ q' : ι → ℝ, (∀ i, 0 ≤ q' i) ∧ (∑ i, q' i = r) ∧
      (∀ i, q i = 0 → q' i = 0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤ k+d+1+H ∧
      (∀ h, (∑ i, q' i*D i h) = ∑ i, q i*D i h) ∧
      (∀ g, (∑ i, q' i*F i g) = ∑ i, q i*F i g) ∧
      Cuts M r q' (fun i => v i-η) := by
  classical
  obtain ⟨q', hq', hmass', hsupp, hcard, hmom⟩ :=
    finite_feature_compression ((Fin k ⊕ Fin d) ⊕ Fin H) q (extraSparseFeatures k d H D F v M r η) r hq hmass hr
  refine ⟨q', hq', hmass', hsupp, ?_, ?_, (fun g => hmom (Sum.inl (Sum.inr g))), ?_⟩
  · simpa only [Fintype.card_sum, Fintype.card_fin, Nat.add_right_comm (k+d) H 1] using hcard
  · intro h
    exact hmom (Sum.inl (Sum.inl h))
  · apply call_bound_implies_cuts q' (fun i => v i-η) M r hM hq' hmass'
    apply finite_grid_implication q' v M r η H hM (le_of_lt hr) hη hH hq'
    · intro i hi
      exact supported_score_cap q v M r hM hq hcuts i (fun hzero => hi (hsupp i hzero))
    · intro l hl hlH
      let j : Fin H := ⟨l-1, by omega⟩
      have hj : j.val+1 = l := by dsimp [j]; omega
      have hm := hmom (Sum.inr j)
      change (∑ i, q' i*max (v i-(M*r-gridNode M r η (j.val+1))) 0) =
        ∑ i, q i*max (v i-(M*r-gridNode M r η (j.val+1))) 0 at hm
      rw [hj] at hm
      change (∑ i, q' i*max (v i-(M*r-gridNode M r η l)) 0) ≤ _
      rw [hm]
      exact cuts_imply_call_bound q v M r hM hcuts _

theorem exact_sparse_cut_witness_extra_moments {ι : Type*} [Fintype ι]
    (k d H : ℕ) (D : ι → Fin k → ℝ) (F : ι → Fin d → ℝ) (p : Fin k → ℝ) (q v : ι → ℝ) (M r η : ℝ)
    (hM : 0 < M) (hr : 0 < r) (hη : 0 < η)
    (hH : M*r ≤ η*(H:ℝ)^2) (hq : ∀ i, 0 ≤ q i)
    (hmass : ∑ i, q i = r) (hcuts : Cuts M r q v)
    (hv : ∀ i, v i = ∑ h, D i h*p h) (hmean : ∑ i, q i*v i = 0)
    (hlow : ∀ i, q i ≠ 0 → -M*r ≤ v i) :
    ∃ q' : ι → ℝ, (∀ i, 0 ≤ q' i) ∧ (∑ i, q' i = r) ∧
      (∀ i, q i = 0 → q' i = 0) ∧
      (Finset.univ.filter fun i => q' i ≠ 0).card ≤ k+d+H ∧
      (∀ h, (∑ i, q' i*D i h) = ∑ i, q i*D i h) ∧
      (∀ g, (∑ i, q' i*F i g) = ∑ i, q i*F i g) ∧
      Cuts M r q' (fun i => v i-η) := by
  classical
  have hHpos : 0 < H := by
    by_contra hn
    have hzero : H = 0 := by omega
    subst H
    norm_num at hH
    nlinarith [mul_pos hM hr]
  obtain ⟨q', hq', hmass', hsupp, hcard, hmom⟩ :=
    finite_feature_compression ((Fin k ⊕ Fin d) ⊕ Fin (H-1)) q (extraSparseFeatures k d (H-1) D F v M r η) r hq hmass hr
  have hanchor : ∀ h, (∑ i, q' i*D i h) = ∑ i, q i*D i h := fun h => hmom (Sum.inl (Sum.inl h))
  refine ⟨q', hq', hmass', hsupp, ?_, hanchor, (fun g => hmom (Sum.inl (Sum.inr g))), ?_⟩
  · simp only [Fintype.card_sum, Fintype.card_fin] at hcard
    omega
  · apply call_bound_implies_cuts q' (fun i => v i-η) M r hM hq' hmass'
    apply finite_grid_implication q' v M r η H hM (le_of_lt hr) hη hH hq'
    · intro i hi
      exact supported_score_cap q v M r hM hq hcuts i (fun hzero => hi (hsupp i hzero))
    · intro l hl hlH
      by_cases hlast : l = H
      · subst l
        have hnode : gridNode M r η H = 2*M*r := min_eq_right (by nlinarith)
        rw [hnode]
        have harg : M*r-2*M*r = -M*r := by ring
        rw [harg]
        have hmean' : ∑ i, q' i*v i = 0 :=
          (linear_score_moment_preserved k D p q q' v hv hanchor).trans hmean
        rw [bottom_call_of_zero_mean q' v M r hmass' hmean'
          (fun i hi => hlow i (fun hzero => hi (hsupp i hzero)))]
        have heq : envelope M r (-M*r) = M*r^2 := by
          unfold envelope
          field_simp
          ring
        rw [heq]
      · have hlt : l < H := lt_of_le_of_ne hlH hlast
        let j : Fin (H-1) := ⟨l-1, by omega⟩
        have hj : j.val+1 = l := by dsimp [j]; omega
        have hm := hmom (Sum.inr j)
        change (∑ i, q' i*max (v i-(M*r-gridNode M r η (j.val+1))) 0) =
          ∑ i, q i*max (v i-(M*r-gridNode M r η (j.val+1))) 0 at hm
        rw [hj] at hm
        change (∑ i, q' i*max (v i-(M*r-gridNode M r η l)) 0) ≤ _
        rw [hm]
        exact cuts_imply_call_bound q v M r hM hcuts _

end
end SparseCompletion
