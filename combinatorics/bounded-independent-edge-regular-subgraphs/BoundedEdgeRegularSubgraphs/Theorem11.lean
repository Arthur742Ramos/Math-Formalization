module

public import BoundedEdgeRegularSubgraphs.Model
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Statements of Theorem 1.1

These are proposition-valued definitions for the four parts of the theorem.
The proofs of the lower bounds are open tasks in this package.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

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

end BoundedEdgeRegularSubgraphs
