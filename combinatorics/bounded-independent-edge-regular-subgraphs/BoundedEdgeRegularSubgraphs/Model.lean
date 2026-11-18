module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Distributions.Bernoulli

/-!
# Independent edges on a finite vertex set

Each unordered pair is represented by its increasing orientation. The finite product
law makes these edge coordinates independent.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

/-- An unordered pair of distinct vertices, represented in increasing order. -/
def Edge (α : Type*) [LT α] := {e : α × α // e.1 < e.2}

instance {α : Type*} [Fintype α] [LinearOrder α] : Fintype (Edge α) :=
  inferInstanceAs (Fintype {e : α × α // e.1 < e.2})

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- Sum the weights of the edges incident with a vertex. -/
noncomputable def degreeSum (w : Edge α → ℝ) (i : α) : ℝ :=
  ∑ e : Edge α, if i = e.val.1 ∨ i = e.val.2 then w e else 0

/-- The average of a vector indexed by the vertex set. -/
noncomputable def vertexMean (u : α → ℝ) : ℝ :=
  (∑ i, u i) / Fintype.card α

/-- Sum of squared deviations of the expected degrees from their mean. -/
noncomputable def degreeVariation (p : Edge α → Set.Icc (0 : ℝ) 1) : ℝ :=
  ∑ i, (degreeSum (fun e ↦ (p e : ℝ)) i -
    vertexMean (degreeSum (fun e ↦ (p e : ℝ)))) ^ 2

/-- The product of the Bernoulli laws with mass p(e) at 1 and 1 - p(e) at 0. -/
noncomputable def graphLaw (p : Edge α → Set.Icc (0 : ℝ) 1) :
    Measure (Edge α → ℝ) :=
  Measure.pi (fun e ↦ bernoulliMeasure (1 : ℝ) 0 (p e))

/-- Outcomes with a common degree on the whole vertex set. -/
noncomputable def regularEvent : Set (Edge α → ℝ) :=
  {w | ∀ i j, degreeSum w i = degreeSum w j}

/-- View an edge of the induced vertex set as an edge of the ambient graph. -/
def inducedEdge (S : Finset α) (e : Edge ↥S) : Edge α :=
  ⟨(e.val.1.val, e.val.2.val), e.property⟩

/-- Restriction of edge data to pairs within the vertex set. -/
def induce {β : Type*} (S : Finset α) (w : Edge α → β) (e : Edge ↥S) : β :=
  w (inducedEdge S e)

/-- Outcomes with a regular induced subgraph on the specified vertex set. -/
noncomputable def inducedRegularEvent (S : Finset α) : Set (Edge α → ℝ) :=
  induce S ⁻¹' regularEvent

/-- Outcomes with a regular induced subgraph of exactly k vertices. -/
noncomputable def exactOrderEvent (k : ℕ) : Set (Edge α → ℝ) :=
  ⋃ S : {S : Finset α // S.card = k}, inducedRegularEvent S.val

/-- Outcomes with a regular induced subgraph on at least k vertices. -/
noncomputable def atLeastOrderEvent (k : ℕ) : Set (Edge α → ℝ) :=
  ⋃ S : {S : Finset α // k ≤ S.card}, inducedRegularEvent S.val

end BoundedEdgeRegularSubgraphs
