module

public import RemainingStatements
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition

open Filter Finset OpenProblems
open scoped Classical

/-- Lemma 9 for the graph and cutoffs in Sections 3–5. Coordinates may come from
overlapping sets. Each positional set is disjoint from the test set. -/
theorem conditional_range_on_core (u τ c θ : ℝ) (hu : 0 < u) (hτ : 0 < τ) (hτ' : τ ≤ 1)
    (hθ : 0 < θ) (L : ℕ) (D : ℝ) (hD : D ≤ θ * (u/16) * L / 10) :
    ∃ β mass : ℝ, 0 < β ∧ 0 < mass ∧ ∀ᶠ r : ℕ in atTop, ∀ (N : ℕ)
      (G : SimpleGraph (Fin N)) (B Y : Finset (Fin N)) (Xs : List (Finset (Fin N)))
      (Q : Finset (List (Fin N))), Core G B r u τ c → Positional B Y Xs r u →
      Xs.length = L → Q ⊆ tupleSpace Xs → Real.exp (-D*r) * (tupleSpace Xs).card ≤ Q.card →
      ∃ E ⊆ Y, (E.card : ℝ) ≤ Real.exp (-β*r) * Y.card ∧ ∀ y ∈ Y, y ∉ E →
        ∃ lowCount highCount : ℕ, (lowCount : ℝ) ≤ θ*L/5 ∧ (1-θ/5)*L ≤ (highCount : ℝ) ∧
          mass * Q.card ≤ ((Q.filter fun p => tupleDegree (adj G) y p = lowCount).card : ℝ) ∧
          mass * Q.card ≤ ((Q.filter fun p => tupleDegree (adj G) y p = highCount).card : ℝ) := by
  obtain ⟨β,m,hβ,hm,n,h⟩ := conditional_range u τ θ hu hτ hτ' hθ L D hD
  refine ⟨β,m,hβ,hm,?_⟩
  filter_upwards [eventually_ge_atTop n] with r hr
  intro N G B Y Xs Q core pos hL hQ hmass
  have hB : 0 < (B.card : ℝ) := pos_of_mul_pos_left
    ((Real.exp_pos _).trans_le core.1) (Real.exp_pos _).le
  apply h r hr (adj G) (B.card : ℝ) hB Xs Y Q hL hQ hmass
    pos.1.2 (fun X hX => (pos.2 X hX).1.2)
  intro b X hX U hUY hU Z hZX hZ
  have cut := core.2 Z (hZX.trans (pos.2 X hX).1.1) U (hUY.trans pos.1.1)
    ((pos.2 X hX).2.mono hZX hUY) hZ hU b
  have symm (x y : Fin N) : adj G x y = adj G y x := by
    simp only [adj, G.adj_comm x y]
  simpa only [symm, mul_left_comm, mul_assoc, mul_comm] using cut

end InducedDegreeRepetition
