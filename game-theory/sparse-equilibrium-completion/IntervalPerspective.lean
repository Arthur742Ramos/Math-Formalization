/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import CompletionCriterion
public import GameModel

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def perspectiveRecover (lo V q : ℝ) : ℝ := if q=0 then lo else V/q

theorem perspective_zero (lo hi V q : ℝ) (hq : q=0)
    (hlo : lo*q ≤ V) (hhi : V ≤ hi*q) : V=0 := by
  subst q
  simp only [mul_zero] at hlo hhi
  exact le_antisymm hhi hlo

theorem perspective_recover_bounds (lo hi V q : ℝ) (hq : 0 ≤ q) (hlu : lo ≤ hi)
    (hlo : lo*q ≤ V) (hhi : V ≤ hi*q) :
    lo ≤ perspectiveRecover lo V q ∧ perspectiveRecover lo V q ≤ hi ∧
      q*perspectiveRecover lo V q=V := by
  by_cases hz : q=0
  · have hv := perspective_zero lo hi V q hz hlo hhi
    simp only [perspectiveRecover,hz,ite_true,zero_mul]
    exact ⟨le_refl _,hlu,hv.symm⟩
  · have hp : 0 < q := lt_of_le_of_ne hq (Ne.symm hz)
    simp only [perspectiveRecover,ite_eq_right hz]
    refine ⟨(le_div_iff₀ hp).mpr hlo,(div_le_iff₀ hp).mpr hhi,?_⟩
    field_simp

def intervalCrossRecover {ι α : Type*} (lo V : ι → α → ℝ) (q : ι → ℝ) : ι → α → ℝ :=
  fun i h => perspectiveRecover (lo i h) (V i h) (q i)

def intervalMomentScore {ι α : Type*} [Fintype α] (p : α → ℝ) (V : ι → α → ℝ) : ι → ℝ :=
  fun i => ∑ h, p h*V i h

theorem interval_recovered_cross_bounds {ι α : Type*} (lo hi V : ι → α → ℝ) (q : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hlu : ∀ i h, lo i h ≤ hi i h)
    (hlo : ∀ i h, lo i h*q i ≤ V i h) (hhi : ∀ i h, V i h ≤ hi i h*q i) :
    (∀ i h, lo i h ≤ intervalCrossRecover lo V q i h ∧ intervalCrossRecover lo V q i h ≤ hi i h) ∧
      ∀ i h, q i*intervalCrossRecover lo V q i h=V i h := by
  constructor
  · intro i h
    exact ⟨(perspective_recover_bounds _ _ _ _ (hq i) (hlu i h) (hlo i h) (hhi i h)).1,
      (perspective_recover_bounds _ _ _ _ (hq i) (hlu i h) (hlo i h) (hhi i h)).2.1⟩
  · intro i h
    exact (perspective_recover_bounds _ _ _ _ (hq i) (hlu i h) (hlo i h) (hhi i h)).2.2

theorem interval_recovered_score_moment {ι α : Type*} [Fintype α]
    (lo V : ι → α → ℝ) (p : α → ℝ) (q : ι → ℝ)
    (hm : ∀ i h, q i*intervalCrossRecover lo V q i h=V i h) (i : ι) :
    q i*score (intervalCrossRecover lo V q) p i=intervalMomentScore p V i := by
  unfold score intervalMomentScore
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  calc
    _ = p h*(q i*intervalCrossRecover lo V q i h) := by ring
    _ = _ := by rw [hm i h]

end
end SparseCompletion
