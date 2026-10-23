/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.GapCertificates

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def fixedAnchorFeasible {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Set (ι → ℝ)) (K : α → α → ℝ) (D : ι → α → ℝ)
    (p : α → ℝ) (M r ρ : ℝ) : Prop :=
  ∃ q ∈ R, (∀ i, 0 ≤ q i) ∧ (∑ i, q i)=r ∧
    ∃ B : ι → ι → ℝ, IsSkew B ∧ (∀ i j, -M ≤ B i j ∧ B i j ≤ M) ∧
      ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ρ

def fixedAnchorGapFeasible {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Set (ι → ℝ)) (K : α → α → ℝ) (D : ι → α → ℝ)
    (p : α → ℝ) (M r ρ η : ℝ) : Prop :=
  ∃ q ∈ R, fixedAnchorGapPoint K D p q M r ρ η

theorem feasible_implies_gap_feasible {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Set (ι → ℝ)) (K : α → α → ℝ) (D : ι → α → ℝ)
    (p : α → ℝ) (M r ρ η : ℝ) (hM : 0 < M)
    (h : fixedAnchorFeasible R K D p M r ρ) :
    fixedAnchorGapFeasible R K D p M r ρ η := by
  rcases h with ⟨q,hR,hq,hr,B,hB,hb,hrows⟩
  exact ⟨q,hR,exact_completion_gap_point K D B p q M r ρ η hM hq hr hB hb hrows⟩

theorem gap_feasible_implies_relaxed_feasible {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Set (ι → ℝ)) (K : α → α → ℝ) (D : ι → α → ℝ)
    (p : α → ℝ) (M r ρ η : ℝ) (hM : 0 < M) (hr : 0 ≤ r) (hη : 0 < η)
    (h : fixedAnchorGapFeasible R K D p M r ρ η) :
    fixedAnchorFeasible R K D p M r (ρ+η) := by
  rcases h with ⟨q,hR,hpoint⟩
  exact ⟨q,hR,hpoint.1,hpoint.2.1,gap_point_completed_witness K D p q M r ρ η hM hr hη hpoint⟩

theorem gap_infeasible_excludes_completion {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Set (ι → ℝ)) (K : α → α → ℝ) (D : ι → α → ℝ)
    (p : α → ℝ) (M r ρ η : ℝ) (hM : 0 < M)
    (h : ¬fixedAnchorGapFeasible R K D p M r ρ η) :
    ¬fixedAnchorFeasible R K D p M r ρ :=
  fun hf => h (feasible_implies_gap_feasible R K D p M r ρ η hM hf)

theorem gap_feasibility_monotone {ι α : Type*} [Fintype ι] [Fintype α]
    (R : Set (ι → ℝ)) (K : α → α → ℝ) (D : ι → α → ℝ)
    (p : α → ℝ) (M r ρ ρ' η : ℝ) (hρ : ρ ≤ ρ')
    (h : fixedAnchorGapFeasible R K D p M r ρ η) :
    fixedAnchorGapFeasible R K D p M r ρ' η := by
  rcases h with ⟨q,hR,hpoint⟩
  exact ⟨q,hR,fixed_anchor_gap_monotone K D p q M r ρ ρ' η hρ hpoint⟩

end
end SparseCompletion
