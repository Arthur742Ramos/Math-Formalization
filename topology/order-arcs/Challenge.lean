/-
Copyright (c) 2026 Arthur Freitas Ramos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos
-/
module

public import Mathlib.Topology.MetricSpace.Closeds
public import Mathlib.Topology.UnitInterval
public import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! An order arc between properly nested subcontinua of a compact metric space.
The ambient space need not be connected. The single theorem hole is intentional;
the independent Solution proves the statement. -/
@[expose] public section
open Set Topology TopologicalSpace Metric
namespace OrderArcs

noncomputable def height {X : Type*} [mX : MetricSpace X] (q : ℕ → X)
    (K : NonemptyCompacts X) : ℝ :=
  -∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) * infDist (q n) (K : Set X)

abbrev ContinuumInterval {X : Type*} [tX : TopologicalSpace X] (A B : NonemptyCompacts X) :=
  {K : NonemptyCompacts X // A ≤ K ∧ K ≤ B ∧ IsConnected (K : Set X)}

theorem exists_order_arc {X : Type*} [mX : MetricSpace X] [cX : CompactSpace X]
    (A B : NonemptyCompacts X) (hA : IsConnected (A : Set X))
    (hB : IsConnected (B : Set X)) (hAB : A < B) :
    ∃ γ : unitInterval → NonemptyCompacts X,
      Continuous γ ∧ IsEmbedding γ ∧ γ 0 = A ∧ γ 1 = B ∧
      (∀ t : unitInterval, IsConnected (γ t : Set X)) ∧ StrictMono γ := by
  sorry

end OrderArcs
