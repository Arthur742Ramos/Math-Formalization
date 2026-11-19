module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Uniform regular induced subgraph bounds

This statement module selects the four parts of Theorem 1.1 from
*Regular induced subgraphs in bounded independent-edge arrays*.
The finite product law assigns independently to each pair an edge
with its specified probability. The events distinguish a subgraph
of exactly the prescribed order from a subgraph whose order is at
least the prescribed threshold.

The statements below are Comparator placeholders. The proof module
exports the corresponding theorems without importing this module.
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

/-- Every edge probability belongs to the common closed interval. -/
def HasFloor {n : ℕ} (ξ : ℝ) (p : Edge (Fin n) → Set.Icc (0 : ℝ) 1) : Prop :=
  ∀ e, ξ ≤ (p e : ℝ) ∧ (p e : ℝ) ≤ 1 - ξ

/-- All expected degrees in the ambient random graph coincide. -/
def EqualExpectedDegrees {n : ℕ} (p : Edge (Fin n) → Set.Icc (0 : ℝ) 1) : Prop :=
  ∀ i j, degreeSum (fun e ↦ (p e : ℝ)) i = degreeSum (fun e ↦ (p e : ℝ)) j

/-- A bounded real symmetric matrix of rank at most r extends the array. -/
noncomputable def HasRankCompletion {n : ℕ} (r : ℕ)
    (p : Edge (Fin n) → Set.Icc (0 : ℝ) 1) : Prop :=
  ∃ A : Matrix (Fin n) (Fin n) ℝ, (∀ i j, A i j = A j i) ∧
    (∀ i j, A i j ∈ Set.Icc (0 : ℝ) 1) ∧ A.rank ≤ r ∧
    ∀ e, A e.val.1 e.val.2 = (p e : ℝ)

/-- The first-variable Lipschitz condition for the maximum norm on the cube. -/
def CubeLipschitz {d : ℕ} (L : ℝ)
    (W : (Fin d → Set.Icc (0 : ℝ) 1) → (Fin d → Set.Icc (0 : ℝ) 1) →
      Set.Icc (0 : ℝ) 1) : Prop :=
  ∀ x y z ε, 0 ≤ ε → (∀ i, |(x i : ℝ) - y i| ≤ ε) →
    |(W x z : ℝ) - W y z| ≤ L * ε

/-- Theorem 1.1(1), with both failure bounds and the possibly smaller second threshold. -/
noncomputable def Theorem1_1_arbitrary : Prop :=
  ∀ ξ : ℝ, 0 < ξ → ξ < 1 / 2 →
    ∃ c c' : ℝ, 0 < c' ∧ c' ≤ c ∧ ∃ n₀ : ℕ, 1 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ p : Edge (Fin n) → Set.Icc (0 : ℝ) 1, HasFloor ξ p →
        (graphLaw p).real (atLeastOrderEvent ⌈c * Real.log n ^ 2⌉₊)ᶜ ≤ (n : ℝ)⁻¹ ∧
        (graphLaw p).real (atLeastOrderEvent ⌈c' * Real.log n ^ 2⌉₊)ᶜ ≤
          Real.exp (-Real.sqrt n * Real.log n / 8)

/-- Theorem 1.1(2), uniformly over equal-expected-degree arrays. -/
noncomputable def Theorem1_1_equalDegrees : Prop :=
  ∀ ξ : ℝ, 0 < ξ → ξ < 1 / 2 →
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧ ∃ k₀ n₀ : ℕ, 1 ≤ k₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ k : ℕ, k₀ ≤ k → (k : ℝ) ≤ a * (n : ℝ) ^ (2 / 3 : ℝ) →
        ∀ p : Edge (Fin n) → Set.Icc (0 : ℝ) 1, HasFloor ξ p → EqualExpectedDegrees p →
          (graphLaw p).real (exactOrderEvent k)ᶜ ≤
            Real.exp (-c * n / (k : ℝ) ^ (3 / 2 : ℝ))

/-- Theorem 1.1(3), uniformly over kernels and assignments with the specified bounds. -/
noncomputable def Theorem1_1_lipschitz : Prop :=
  ∀ (ξ L : ℝ) (d : ℕ), 0 < ξ → ξ < 1 / 2 → 0 ≤ L → 0 < d →
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧ ∃ k₀ n₀ : ℕ, 1 ≤ k₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ k : ℕ, k₀ ≤ k →
        (k : ℝ) ≤ a * (n : ℝ) ^ (2 / ((d : ℝ) + 3)) →
        ∀ W : (Fin d → Set.Icc (0 : ℝ) 1) → (Fin d → Set.Icc (0 : ℝ) 1) →
          Set.Icc (0 : ℝ) 1,
          (∀ x y, W x y = W y x) → CubeLipschitz L W →
          (∀ x y, ξ ≤ (W x y : ℝ) ∧ (W x y : ℝ) ≤ 1 - ξ) →
          ∀ x : Fin n → (Fin d → Set.Icc (0 : ℝ) 1),
            (graphLaw (fun e ↦ W (x e.val.1) (x e.val.2))).real (exactOrderEvent k)ᶜ ≤
              Real.exp (-c * n / (k : ℝ) ^ (3 / 2 : ℝ))

/-- Theorem 1.1(4), uniformly over arrays admitting a bounded rank completion. -/
noncomputable def Theorem1_1_lowRank : Prop :=
  ∀ (ξ : ℝ) (r : ℕ), 0 < ξ → ξ < 1 / 2 → 0 < r →
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧ ∃ k₀ n₀ : ℕ, 1 ≤ k₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ k : ℕ, k₀ ≤ k →
        (k : ℝ) ≤ a * (n : ℝ) ^ (4 / ((r : ℝ) + 7)) →
        ∀ p : Edge (Fin n) → Set.Icc (0 : ℝ) 1, HasFloor ξ p → HasRankCompletion r p →
          (graphLaw p).real (exactOrderEvent k)ᶜ ≤
            Real.exp (-c * n / (k : ℝ) ^ (3 / 2 : ℝ))

/-- The two logarithmic bounds for arbitrary edge arrays. -/
theorem theorem1_1_arbitrary : Theorem1_1_arbitrary := by
  sorry

/-- The exact-order bound for equal expected degrees. -/
theorem theorem1_1_equalDegrees : Theorem1_1_equalDegrees := by
  sorry

/-- The exact-order bound for Lipschitz kernels. -/
theorem theorem1_1_lipschitz : Theorem1_1_lipschitz := by
  sorry

/-- The exact-order bound for bounded rank completions. -/
theorem theorem1_1_lowRank : Theorem1_1_lowRank := by
  sorry

end BoundedEdgeRegularSubgraphs
