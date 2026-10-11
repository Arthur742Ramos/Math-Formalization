/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz
-/
module

public import Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.UnitInterval

/-!
# Dowker's countable paracompactness and insertion properties

The countable covering property below is stated using ordinary open-cover
refinements, independently of the characterization theorems.
AI implementation and review contributions are recorded in the project provenance.
-/

@[expose] public section

open Set

namespace Dowker

universe u

/-- Every countable family of open sets covering `X` has a locally finite open
refinement. The refinement may have any cardinality. -/
def CountablyParacompact (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ U : Set (Set X), U.Countable → (∀ s ∈ U, IsOpen s) → ⋃₀ U = univ →
    ∃ V : Set (Set X), (∀ s ∈ V, IsOpen s) ∧ ⋃₀ V = univ ∧
      LocallyFinite (fun s : V => (s : Set X)) ∧ ∀ s ∈ V, ∃ t ∈ U, s ⊆ t

/-- Strict insertion for arbitrary real semicontinuous bounds, with no
boundedness or uniform-gap condition. -/
def StrictInsertion (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ h g : X → ℝ, UpperSemicontinuous h → LowerSemicontinuous g →
    (∀ x, h x < g x) → ∃ f : X → ℝ, Continuous f ∧ ∀ x, h x < f x ∧ f x < g x

end Dowker
