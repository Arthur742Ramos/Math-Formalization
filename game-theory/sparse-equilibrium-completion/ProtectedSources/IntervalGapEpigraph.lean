/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.IntervalGapGame

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def intervalGapEpigraphPoint {ι α : Type*} [Fintype ι] [Fintype α]
    (K : α → α → ℝ) (lo hi V : ι → α → ℝ) (p : α → ℝ) (q : ι → ℝ)
    (M r ρ η : ℝ) (a : Fin (gridSize M r η) → ι → ℝ) : Prop :=
  (∀ i, 0 ≤ q i) ∧ (∑ i, q i)=r ∧
  (∀ i h, lo i h*q i ≤ V i h ∧ V i h ≤ hi i h*q i) ∧
  (∀ h, (∑ b, K h b*p b)-(∑ i, V i h) ≤ ρ) ∧
  (∀ i, score lo p i ≤ ρ+M*r) ∧
  (∀ i, intervalMomentScore p V i ≤ (ρ+M*r)*q i) ∧
  ∀ l : Fin (gridSize M r η),
    (∀ i, 0 ≤ a l i) ∧
    (∀ i, intervalMomentScore p V i-(ρ+(M*r-gridNode M r η (l.val+1)))*q i ≤ a l i) ∧
    (∑ i, a l i) ≤ envelope M r (M*r-gridNode M r η (l.val+1))

theorem interval_gap_epigraph_iff {ι α : Type*} [Fintype ι] [Fintype α]
    (K : α → α → ℝ) (lo hi V : ι → α → ℝ) (p : α → ℝ) (q : ι → ℝ)
    (M r ρ η : ℝ) :
    intervalGapPoint K lo hi V p q M r ρ η ↔ ∃ a, intervalGapEpigraphPoint K lo hi V p q M r ρ η a := by
  constructor
  · rintro ⟨hq,hm,hV,ha,hg,hcap,hcalls⟩
    let a := fun (l : Fin (gridSize M r η)) i =>
      max (intervalMomentScore p V i-(ρ+(M*r-gridNode M r η (l.val+1)))*q i) 0
    refine ⟨a,hq,hm,hV,ha,hg,hcap,?_⟩
    intro l
    exact ⟨fun i => le_max_right _ _,fun i => le_max_left _ _,
      hcalls (l.val+1) (by omega) (by omega)⟩
  · rintro ⟨a,hq,hm,hV,ha,hg,hcap,hcalls⟩
    refine ⟨hq,hm,hV,ha,hg,hcap,?_⟩
    intro l hl hL
    let u : Fin (gridSize M r η) := ⟨l-1,by omega⟩
    have he : u.val+1=l := by dsimp only [u]; omega
    have hh := (perspective_call_epigraph_iff q (intervalMomentScore p V) ρ
      (M*r-gridNode M r η (u.val+1)) (envelope M r (M*r-gridNode M r η (u.val+1)))).mpr
        ⟨a u,hcalls u⟩
    simpa only [he] using hh

end
end SparseCompletion
