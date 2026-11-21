module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Asymptotics.Defs

@[expose] public section

namespace InducedDegreeRepetition

variable {V : Type*}

/-- The degree in the graph induced on S, when x belongs to S. -/
noncomputable def degreeOn (G : SimpleGraph V) (S : Finset V) (x : V) : ℕ := by
  classical exact (S.filter (G.Adj x)).card

noncomputable def degreeClass (G : SimpleGraph V) (S : Finset V) (d : ℕ) : Finset V := by
  classical exact S.filter fun x => degreeOn G S x = d

/-- The paper's Theorem 1, with a witness for the repeated degree. -/
def LogScaleRepetition : Prop :=
  ∀ K : ℝ, 0 < K → ∀ η : ℝ, 0 < η → η < 1 → ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ G : SimpleGraph (Fin N), ∃ S : Finset (Fin N), ∃ d : ℕ,
      ⌈K * Real.log N⌉₊ ≤ S.card ∧ S.card < 2 * ⌈K * Real.log N⌉₊ ∧
      (1 - η) * S.card ≤ ((degreeClass G S d).card : ℝ)

/-- Caro and Yuster use hosts of order strictly greater than n. -/
def Forces (k n : ℕ) : Prop :=
  ∀ N > n, ∀ G : SimpleGraph (Fin N), ∃ S : Finset (Fin N), ∃ d, k ≤ (degreeClass G S d).card

noncomputable def threshold (k : ℕ) : ℕ := sInf {n | Forces k n}

def SubexponentialThreshold : Prop :=
  (fun k : ℕ => Real.log (threshold k)) =o[Filter.atTop] (fun k : ℕ => (k : ℝ))

end InducedDegreeRepetition
