/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import GapCompact
public import ValueBounds

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem gap_threshold_minimal_nonnegative {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Set (ι → ℝ)) (K : α → α → ℝ) (D : ι → α → ℝ) (p : α → ℝ)
    (M r η ρ : ℝ) (hR : IsCompact R) (hne : (gapPairs R K D p M r η).Nonempty)
    (hρ : 0 ≤ ρ) (hgap : fixedAnchorGapFeasible R K D p M r ρ η) :
    gapThresholdValue R K D p M r η ≤ ρ := by
  obtain ⟨q,hq,hpoint,_,hW⟩ := gap_threshold_attained R K D p M r η hR hne
  by_cases hρM : ρ ≤ M
  · obtain ⟨q',hq',hp'⟩ := hgap
    exact gap_threshold_le R K D p M r η ρ hR q' hq' ⟨hρ,hρM⟩ hp'
  · exact le_trans hW (le_of_lt (lt_of_not_ge hρM))

theorem gap_original_infimum_eq {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Set (ι → ℝ)) (K : α → α → ℝ) (D : ι → α → ℝ) (p : α → ℝ)
    (M r η : ℝ) (hR : IsCompact R) (hne : (gapPairs R K D p M r η).Nonempty) :
    sInf {ρ : ℝ | 0 ≤ ρ ∧ fixedAnchorGapFeasible R K D p M r ρ η}=
      gapThresholdValue R K D p M r η := by
  obtain ⟨q,hq,hpoint,hW0,_⟩ := gap_threshold_attained R K D p M r η hR hne
  have hmem : gapThresholdValue R K D p M r η ∈
      {ρ : ℝ | 0 ≤ ρ ∧ fixedAnchorGapFeasible R K D p M r ρ η} := ⟨hW0,q,hq,hpoint⟩
  apply le_antisymm
  · exact csInf_le ⟨0,fun _ h => h.1⟩ hmem
  · exact le_csInf ⟨_,hmem⟩ fun ρ h => gap_threshold_minimal_nonnegative R K D p M r η ρ hR hne h.1 h.2

theorem fixed_anchor_additive_value_enclosure {ι α : Type*} [Fintype ι] [Fintype α]
    [Nonempty (α ⊕ ι)] (K : α → α → ℝ) (D : ι → α → ℝ) (p : α → ℝ)
    (M r η : ℝ) (R : Set (ι → ℝ)) (hM : 0 < M) (hr : 0 ≤ r) (hη : 0 < η)
    (hR : IsCompact R) (hne : R.Nonempty)
    (hp : ∀ h, 0 ≤ p h) (hpm : (∑ h, p h)+r=1)
    (hprob : ∀ q ∈ R, (∀ i, 0 ≤ q i) ∧ (∑ i, q i)=r)
    (hK : IsSkew K) (hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M)
    (hDb : ∀ i h, -M ≤ D i h ∧ D i h ≤ M) :
    0 ≤ gapThresholdValue R K D p M r η ∧ gapThresholdValue R K D p M r η ≤ M ∧
    gapThresholdValue R K D p M r η ≤ fixedGameValue K D p M R ∧
    fixedGameValue K D p M R ≤ gapThresholdValue R K D p M r η+η ∧
    ∃ q ∈ R, ∃ B : ι → ι → ℝ, IsSkew B ∧ (∀ i j, -M ≤ B i j ∧ B i j ≤ M) ∧
      ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ gapThresholdValue R K D p M r η+η := by
  obtain ⟨hV0,hVM,hfeas⟩ := fixed_game_value_bounds K D p M r R (le_of_lt hM) hR hne hp hpm hprob hK hKb hDb
  obtain ⟨q,hq,hpoint⟩ := feasible_implies_gap_feasible R K D p M r (fixedGameValue K D p M R) η hM hfeas
  have hpair : (gapPairs R K D p M r η).Nonempty :=
    ⟨(q,fixedGameValue K D p M R),⟨⟨hq,hV0,hVM⟩,hpoint⟩⟩
  have hWV := gap_threshold_le R K D p M r η _ hR q hq ⟨hV0,hVM⟩ hpoint
  obtain ⟨q',hq',hpoint',hW0,hWM⟩ := gap_threshold_attained R K D p M r η hR hpair
  obtain ⟨B,hB,hb,hrows⟩ := gap_point_completed_witness K D p q' M r _ η hM hr hη hpoint'
  have hV := fixed_game_value_le_witness K D p M R hR B q' ⟨hB,hb⟩ hq'
  have hu := (exploitability_le_iff _ _ _).mpr hrows
  exact ⟨hW0,hWM,hWV,le_trans hV hu,q',hq',B,hB,hb,hrows⟩

end
end SparseCompletion
