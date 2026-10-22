/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import GapFeasibility
public import OptimisticValue

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem gap_points_closed {ι α : Type*} [Fintype ι] [Fintype α]
    (K : α → α → ℝ) (D : ι → α → ℝ) (p : α → ℝ) (M r η : ℝ) :
    IsClosed {z : (ι → ℝ) × ℝ | fixedAnchorGapPoint K D p z.1 M r z.2 η} := by
  change IsClosed ({z : ((ι → ℝ) × ℝ) | ∀ i, 0 ≤ z.1 i} ∩
    ({z : ((ι → ℝ) × ℝ) | (∑ i, z.1 i)=r} ∩
    ({z : ((ι → ℝ) × ℝ) | ∀ i, score D p i ≤ z.2+M*r} ∩
    ({z : ((ι → ℝ) × ℝ) | ∀ h, anchorResponse K D p z.1 h ≤ z.2} ∩
    {z : ((ι → ℝ) × ℝ) | ∀ l : ℕ, 1 ≤ l → l ≤ gridSize M r η →
      call z.1 (fun i => score D p i-z.2) (M*r-gridNode M r η l) ≤
        envelope M r (M*r-gridNode M r η l)}))))
  simp only [Set.ofPred_forall]
  apply IsClosed.inter
  · apply isClosed_iInter
    intro i
    exact isClosed_le continuous_const (show Continuous (fun z : ((ι → ℝ) × ℝ) => z.1 i) by fun_prop)
  · apply IsClosed.inter
    · exact isClosed_eq (show Continuous (fun z : ((ι → ℝ) × ℝ) => ∑ i, z.1 i) by fun_prop) continuous_const
    · apply IsClosed.inter
      · apply isClosed_iInter
        intro i
        exact isClosed_le continuous_const (show Continuous (fun z : ((ι → ℝ) × ℝ) => z.2+M*r) by fun_prop)
      · apply IsClosed.inter
        · apply isClosed_iInter
          intro h
          exact isClosed_le (show Continuous (fun z : ((ι → ℝ) × ℝ) => anchorResponse K D p z.1 h) by
            unfold anchorResponse; fun_prop) continuous_snd
        · apply isClosed_iInter
          intro l
          apply isClosed_iInter
          intro _
          apply isClosed_iInter
          intro _
          exact isClosed_le (show Continuous (fun z : ((ι → ℝ) × ℝ) =>
            call z.1 (fun i => score D p i-z.2) (M*r-gridNode M r η l)) by
              unfold call; fun_prop) continuous_const

def gapPairs {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Set (ι → ℝ)) (K : α → α → ℝ) (D : ι → α → ℝ) (p : α → ℝ)
    (M r η : ℝ) : Set ((ι → ℝ) × ℝ) :=
  (R ×ˢ Set.Icc 0 M) ∩ {z | fixedAnchorGapPoint K D p z.1 M r z.2 η}

theorem gap_pairs_compact {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Set (ι → ℝ)) (K : α → α → ℝ) (D : ι → α → ℝ) (p : α → ℝ)
    (M r η : ℝ) (hR : IsCompact R) : IsCompact (gapPairs R K D p M r η) :=
  (hR.prod isCompact_Icc).inter_right (gap_points_closed K D p M r η)

def gapThresholdValue {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Set (ι → ℝ)) (K : α → α → ℝ) (D : ι → α → ℝ) (p : α → ℝ) (M r η : ℝ) : ℝ :=
  sInf (Prod.snd '' gapPairs R K D p M r η)

theorem gap_threshold_attained {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Set (ι → ℝ)) (K : α → α → ℝ) (D : ι → α → ℝ) (p : α → ℝ)
    (M r η : ℝ) (hR : IsCompact R) (hne : (gapPairs R K D p M r η).Nonempty) :
    ∃ q ∈ R, fixedAnchorGapPoint K D p q M r (gapThresholdValue R K D p M r η) η ∧
      0 ≤ gapThresholdValue R K D p M r η ∧ gapThresholdValue R K D p M r η ≤ M := by
  have hc := (gap_pairs_compact R K D p M r η hR).image continuous_snd
  obtain ⟨⟨q,ρ⟩,⟨⟨hq,hρ⟩,hpoint⟩,he⟩ := hc.sInf_mem (hne.image Prod.snd)
  change ρ=gapThresholdValue R K D p M r η at he
  rw [←he]
  exact ⟨q,hq,hpoint,hρ⟩

theorem gap_threshold_le {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Set (ι → ℝ)) (K : α → α → ℝ) (D : ι → α → ℝ) (p : α → ℝ)
    (M r η ρ : ℝ) (hR : IsCompact R)
    (q : ι → ℝ) (hq : q ∈ R) (hρ : 0 ≤ ρ ∧ ρ ≤ M)
    (hpoint : fixedAnchorGapPoint K D p q M r ρ η) : gapThresholdValue R K D p M r η ≤ ρ := by
  apply csInf_le ((gap_pairs_compact R K D p M r η hR).image continuous_snd).bddBelow
  exact ⟨(q,ρ),⟨⟨hq,hρ⟩,hpoint⟩,rfl⟩

end
end SparseCompletion
