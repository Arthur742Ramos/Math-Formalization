/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import IntervalConic

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def fixedAnchorGapPoint {ι α : Type*} [Fintype ι] [Fintype α]
    (K : α → α → ℝ) (D : ι → α → ℝ) (p : α → ℝ) (q : ι → ℝ)
    (M r ρ η : ℝ) : Prop :=
  (∀ i, 0 ≤ q i) ∧ (∑ i, q i)=r ∧
  (∀ i, score D p i ≤ ρ+M*r) ∧ (∀ h, anchorResponse K D p q h ≤ ρ) ∧
  ∀ l : ℕ, 1 ≤ l → l ≤ gridSize M r η →
    call q (fun i => score D p i-ρ) (M*r-gridNode M r η l) ≤
      envelope M r (M*r-gridNode M r η l)

theorem exact_completion_gap_point {ι α : Type*} [Fintype ι] [Fintype α]
    (K : α → α → ℝ) (D : ι → α → ℝ) (B : ι → ι → ℝ)
    (p : α → ℝ) (q : ι → ℝ) (M r ρ η : ℝ) (hM : 0 < M)
    (hq : ∀ i, 0 ≤ q i) (hr : ∑ i, q i=r) (hB : IsSkew B)
    (hb : ∀ i j, -M ≤ B i j ∧ B i j ≤ M)
    (hrows : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ρ) :
    fixedAnchorGapPoint K D p q M r ρ η := by
  have hh := (block_response_bounds_iff K D B p q ρ).mp hrows
  have hc := (weighted_completion_iff q (score D p) M r ρ (le_of_lt hM) hq hr).mp
    ⟨B,hB,hb,hh.2⟩
  refine ⟨hq,hr,hc.1,hh.1,?_⟩
  intro l _ _
  exact cuts_imply_call_bound q (fun i => score D p i-ρ) M r hM hc.2 _

theorem gap_point_completed_witness {ι α : Type*} [Fintype ι] [Fintype α]
    (K : α → α → ℝ) (D : ι → α → ℝ) (p : α → ℝ) (q : ι → ℝ)
    (M r ρ η : ℝ) (hM : 0 < M) (hr : 0 ≤ r) (hη : 0 < η)
    (h : fixedAnchorGapPoint K D p q M r ρ η) :
    ∃ B : ι → ι → ℝ, IsSkew B ∧ (∀ i j, -M ≤ B i j ∧ B i j ≤ M) ∧
      ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ρ+η := by
  rcases h with ⟨hq,hm,hg,ha,hgrid⟩
  have hcap : ∀ i, q i ≠ 0 → score D p i-ρ ≤ M*r := fun i _ => by linarith [hg i]
  have hc := canonical_grid_implication q (fun i => score D p i-ρ) M r η hM hr hη hq hcap hgrid
  have hcuts := call_bound_implies_cuts q (fun i => (score D p i-ρ)-η) M r hM hq hm hc
  have he : (fun i => (score D p i-ρ)-η)=(fun i => score D p i-(ρ+η)) := by
    funext i
    ring
  rw [he] at hcuts
  obtain ⟨B,hB,hb,hres⟩ :=
    (weighted_completion_iff q (score D p) M r (ρ+η) (le_of_lt hM) hq hm).mpr
      ⟨fun i => by linarith [hg i],hcuts⟩
  refine ⟨B,hB,hb,?_⟩
  apply (block_response_bounds_iff K D B p q (ρ+η)).mpr
  exact ⟨fun h => le_trans (ha h) (by linarith),hres⟩

theorem shifted_call_antitone {ι : Type*} [Fintype ι]
    (q t : ι → ℝ) (ρ ρ' z : ℝ) (hq : ∀ i, 0 ≤ q i) (hρ : ρ ≤ ρ') :
    call q (fun i => t i-ρ') z ≤ call q (fun i => t i-ρ) z := by
  unfold call
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (hq i)
  exact max_le_max (by linarith) (le_refl 0)

theorem fixed_anchor_gap_monotone {ι α : Type*} [Fintype ι] [Fintype α]
    (K : α → α → ℝ) (D : ι → α → ℝ) (p : α → ℝ) (q : ι → ℝ)
    (M r ρ ρ' η : ℝ) (hρ : ρ ≤ ρ')
    (h : fixedAnchorGapPoint K D p q M r ρ η) :
    fixedAnchorGapPoint K D p q M r ρ' η := by
  rcases h with ⟨hq,hm,hg,ha,hgrid⟩
  refine ⟨hq,hm,fun i => by linarith [hg i],fun h => le_trans (ha h) hρ,?_⟩
  intro l hl hH
  exact le_trans (shifted_call_antitone q (score D p) ρ ρ' _ hq hρ) (hgrid l hl hH)

end
end SparseCompletion
