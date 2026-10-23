/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.GapCertificates

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def perspectiveCall {ι : Type*} [Fintype ι] (q H : ι → ℝ) (ρ z : ℝ) : ℝ :=
  ∑ i, max (H i-(ρ+z)*q i) 0

theorem perspective_call_identity {ι : Type*} [Fintype ι]
    (q t H : ι → ℝ) (ρ z : ℝ) (hq : ∀ i, 0 ≤ q i) (hH : ∀ i, q i*t i=H i) :
    call q (fun i => t i-ρ) z=perspectiveCall q H ρ z := by
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_max_of_nonneg _ _ (hq i),mul_zero]
  congr 1
  linear_combination hH i

theorem perspective_call_epigraph_iff {ι : Type*} [Fintype ι]
    (q H : ι → ℝ) (ρ z C : ℝ) :
    perspectiveCall q H ρ z ≤ C ↔
      ∃ a : ι → ℝ, (∀ i, 0 ≤ a i) ∧ (∀ i, H i-(ρ+z)*q i ≤ a i) ∧ (∑ i, a i) ≤ C := by
  constructor
  · intro h
    exact ⟨fun i => max (H i-(ρ+z)*q i) 0,fun i => le_max_right _ _,
      fun i => le_max_left _ _,h⟩
  · rintro ⟨a,ha,hb,hc⟩
    exact le_trans (Finset.sum_le_sum fun i _ => max_le (hb i) (ha i)) hc

def intervalGapPoint {ι α : Type*} [Fintype ι] [Fintype α]
    (K : α → α → ℝ) (lo hi V : ι → α → ℝ) (p : α → ℝ) (q : ι → ℝ)
    (M r ρ η : ℝ) : Prop :=
  (∀ i, 0 ≤ q i) ∧ (∑ i, q i)=r ∧
  (∀ i h, lo i h*q i ≤ V i h ∧ V i h ≤ hi i h*q i) ∧
  (∀ h, (∑ a, K h a*p a)-(∑ i, V i h) ≤ ρ) ∧
  (∀ i, score lo p i ≤ ρ+M*r) ∧
  (∀ i, intervalMomentScore p V i ≤ (ρ+M*r)*q i) ∧
  ∀ l : ℕ, 1 ≤ l → l ≤ gridSize M r η →
    perspectiveCall q (intervalMomentScore p V) ρ (M*r-gridNode M r η l) ≤
      envelope M r (M*r-gridNode M r η l)

theorem interval_gap_recovered_exact_point {ι α : Type*} [Fintype ι] [Fintype α]
    (K : α → α → ℝ) (lo hi V : ι → α → ℝ) (p : α → ℝ) (q : ι → ℝ)
    (M r ρ η : ℝ) (hlu : ∀ i h, lo i h ≤ hi i h)
    (h : intervalGapPoint K lo hi V p q M r ρ η) :
    (∀ i h, lo i h ≤ intervalCrossRecover lo V q i h ∧ intervalCrossRecover lo V q i h ≤ hi i h) ∧
      fixedAnchorGapPoint K (intervalCrossRecover lo V q) p q M r ρ η := by
  rcases h with ⟨hq,hm,hV,ha,hlo,hcap,hgrid⟩
  obtain ⟨hD,hprod⟩ := interval_recovered_cross_bounds lo hi V q hq hlu
    (fun i h => (hV i h).1) (fun i h => (hV i h).2)
  have hH := fun i => interval_recovered_score_moment lo V p q hprod i
  refine ⟨hD,hq,hm,?_,?_,?_⟩
  · intro i
    by_cases hz : q i=0
    · simpa only [score,intervalCrossRecover,perspectiveRecover,hz,ite_true] using hlo i
    · have hp : 0 < q i := lt_of_le_of_ne (hq i) (Ne.symm hz)
      have hc := hcap i
      rw [←hH i] at hc
      exact (mul_le_mul_iff_right₀ hp).mp (by simpa only [mul_comm] using hc)
  · intro a
    rw [anchor_response_of_perspective K _ V p q hprod a]
    exact ha a
  · intro l hl hL
    rw [perspective_call_identity q _ _ ρ _ hq hH]
    exact hgrid l hl hL

theorem interval_gap_completed_witness {ι α : Type*} [Fintype ι] [Fintype α]
    (K : α → α → ℝ) (lo hi V : ι → α → ℝ) (p : α → ℝ) (q : ι → ℝ)
    (M r ρ η : ℝ) (hM : 0 < M) (hr : 0 ≤ r) (hη : 0 < η)
    (hlu : ∀ i h, lo i h ≤ hi i h) (h : intervalGapPoint K lo hi V p q M r ρ η) :
    ∃ (D : ι → α → ℝ) (B : ι → ι → ℝ),
      (∀ i h, lo i h ≤ D i h ∧ D i h ≤ hi i h) ∧ IsSkew B ∧
      (∀ i j, -M ≤ B i j ∧ B i j ≤ M) ∧
      ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ρ+η := by
  obtain ⟨hD,hg⟩ := interval_gap_recovered_exact_point K lo hi V p q M r ρ η hlu h
  obtain ⟨B,hB,hb,hrows⟩ := gap_point_completed_witness K _ p q M r ρ η hM hr hη hg
  exact ⟨intervalCrossRecover lo V q,B,hD,hB,hb,hrows⟩

end
end SparseCompletion
