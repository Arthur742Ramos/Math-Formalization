/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import IntervalGap

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem exact_interval_completion_gap_point {ι α : Type*} [Fintype ι] [Fintype α]
    (K : α → α → ℝ) (lo hi D : ι → α → ℝ) (B : ι → ι → ℝ)
    (p : α → ℝ) (q : ι → ℝ) (M r ρ η : ℝ)
    (hM : 0 < M) (hp : ∀ h, 0 ≤ p h) (hq : ∀ i, 0 ≤ q i) (hr : ∑ i, q i=r)
    (hD : ∀ i h, lo i h ≤ D i h ∧ D i h ≤ hi i h)
    (hB : IsSkew B) (hb : ∀ i j, -M ≤ B i j ∧ B i j ≤ M)
    (hrows : ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ρ) :
    ∃ V, intervalGapPoint K lo hi V p q M r ρ η := by
  have hg := exact_completion_gap_point K D B p q M r ρ η hM hq hr hB hb hrows
  let V := fun i h => q i*D i h
  have hprod : ∀ i h, q i*D i h=V i h := fun _ _ => rfl
  have hH : ∀ i, q i*score D p i=intervalMomentScore p V i := by
    intro i
    unfold score intervalMomentScore
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun h _ => by dsimp only [V]; ring
  refine ⟨V,hq,hr,?_,?_,?_,?_,?_⟩
  · intro i h
    exact ⟨by dsimp only [V]; nlinarith [mul_nonneg (sub_nonneg.mpr (hD i h).1) (hq i)],
      by dsimp only [V]; nlinarith [mul_nonneg (sub_nonneg.mpr (hD i h).2) (hq i)]⟩
  · intro h
    rw [←anchor_response_of_perspective K D V p q hprod h]
    exact hg.2.2.2.1 h
  · intro i
    exact le_trans (score_lower_from_intervals lo D p hp (fun i h => (hD i h).1) i) (hg.2.2.1 i)
  · intro i
    rw [←hH i,mul_comm (q i)]
    exact mul_le_mul_of_nonneg_right (hg.2.2.1 i) (hq i)
  · intro l hl hL
    rw [←perspective_call_identity q (score D p) _ ρ _ hq hH]
    exact hg.2.2.2.2 l hl hL

theorem normalized_interval_gap_completed_witness {ι α : Type*} [Fintype ι] [Fintype α]
    (K : α → α → ℝ) (lo hi V : ι → α → ℝ) (p : α → ℝ) (q : ι → ℝ)
    (M r ρ η : ℝ) (hM : 0 < M) (hr : 0 ≤ r) (hη : 0 < η)
    (hp : ∀ h, 0 ≤ p h) (hm : (∑ h, p h)+r=1)
    (hK : IsSkew K) (hKb : ∀ h h', -M ≤ K h h' ∧ K h h' ≤ M)
    (hlo : ∀ i h, -M ≤ lo i h) (hhi : ∀ i h, hi i h ≤ M)
    (hlu : ∀ i h, lo i h ≤ hi i h) (h : intervalGapPoint K lo hi V p q M r ρ η) :
    ∃ (D : ι → α → ℝ) (B : ι → ι → ℝ),
      (∀ i h, lo i h ≤ D i h ∧ D i h ≤ hi i h) ∧
      (∀ a, 0 ≤ blockWeights p q a) ∧ (∑ a, blockWeights p q a)=1 ∧
      IsSkew (blockMatrix K D B) ∧
      (∀ a b, -M ≤ blockMatrix K D B a b ∧ blockMatrix K D B a b ≤ M) ∧
      ∀ a, response (blockMatrix K D B) (blockWeights p q) a ≤ ρ+η := by
  obtain ⟨D,B,hD,hB,hb,hrows⟩ := interval_gap_completed_witness K lo hi V p q M r ρ η hM hr hη hlu h
  have hDb := fun i a => And.intro (le_trans (hlo i a) (hD i a).1) (le_trans (hD i a).2 (hhi i a))
  refine ⟨D,B,hD,blockWeights_nonneg p q hp h.1,?_,blockMatrix_skew K D B hK hB,
    blockMatrix_bounds K D B M hKb hDb hb,hrows⟩
  rw [blockWeights_mass,h.2.1]
  exact hm

end
end SparseCompletion
