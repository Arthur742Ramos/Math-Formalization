module

public import EditableDraws
public import EditRates
public import SampleFailures
import Mathlib.Tactic.Positivity

public section
namespace InducedDegreeRepetition.Edit

open Filter Finset OpenProblems
open scoped Topology Classical

theorem uniform_rows (u τ c θ : ℝ) (L₀ L₁ : ℕ) (diff : L₀ < L₁)
    (short : RowEstimate u τ c θ L₀ [none])
    (long : RowEstimate u τ c θ L₁ ((moduli L₀).map some ++ [none])) :
    ∃ β w : ℝ, 0 < β ∧ 0 < w ∧ w ≤ 1 ∧ ∀ᶠ r : ℕ in atTop,
      ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (B Y : Finset (Fin N)) (Xs : List (Finset (Fin N)))
        (Q : Finset (List (Fin N))), Core G B r u τ c → Positional B Y Xs r u →
        (Xs.length = L₀ ∨ Xs.length = L₁) → Q ⊆ tupleSpace Xs →
        Real.exp (-budget Xs.length*r)*(tupleSpace Xs).card ≤ Q.card →
        ∃ E ⊆ Y, (E.card:ℝ) ≤ Real.exp (-β*r)*Y.card ∧ ∀ y ∈ Y, y ∉ E →
          ∀ t ∈ requiredTests L₀ Xs.length, Witnesses Q (tupleDegree (adj G) y) Xs.length θ w t := by
  obtain ⟨b,v,bp,vp,hs⟩ := short
  obtain ⟨g,z,gp,zp,hl⟩ := long
  let w := min 1 (min v z)
  refine ⟨min b g,w,lt_min bp gp,lt_min zero_lt_one (lt_min vp zp),min_le_left ..,?_⟩
  filter_upwards [hs,hl] with r hs hl
  intro N G B Y Xs Q core positional len sub mass
  have smaller (x : ℝ) (h : min b g ≤ x) : Real.exp (-x*r)*Y.card ≤ Real.exp (-(min b g)*r)*Y.card :=
    mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg h) (Nat.cast_nonneg _))) (Nat.cast_nonneg _)
  rcases len with h|h <;> rw [h] at mass ⊢
  · obtain ⟨E,ey,e,out⟩ := hs N G B Y Xs Q core positional h sub mass
    refine ⟨E,ey,e.trans (smaller _ (min_le_left ..)),?_⟩
    intro y hy good t ht
    exact witnesses_mono _ _ _ _ _ _ _ ((min_le_right ..).trans (min_le_left ..))
      (out y hy good t (by simpa [requiredTests] using ht))
  · obtain ⟨E,ey,e,out⟩ := hl N G B Y Xs Q core positional h sub mass
    refine ⟨E,ey,e.trans (smaller _ (min_le_right ..)),?_⟩
    intro y hy good t ht
    exact witnesses_mono _ _ _ _ _ _ _ ((min_le_right ..).trans (min_le_right ..))
      (out y hy good t (by simpa [requiredTests,diff.ne'] using ht))

end InducedDegreeRepetition.Edit
