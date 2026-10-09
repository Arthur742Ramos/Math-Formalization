module

/-
Copyright (c) 2026 Arthur Freitas Ramos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos
-/
public import Counterexamples.SorgenfreyLine
public import Mathlib.Topology.Compactness.Lindelof

/-! Independent proposition specifications for the covering theorem package.
This module imports only pinned upstream definitions, and contains no theorem
holes or axioms. `scripts/CompareTypes.lean` checks the solution proofs against
these specifications with ordinary Lean type checking. -/

@[expose] public section

open Set TopologicalSpace
open scoped SorgenfreyLine

universe u

namespace SorgenfreyChallenge

def isLindelof_set : Prop := ∀ A : Set ℝₗ, IsLindelof A

def hereditary_lindelof : Prop := HereditarilyLindelofSpace ℝₗ

def clopen_refinement : Prop :=
  ∀ (A : Set ℝₗ) {ι : Type u} (U : ι → Set A),
    (∀ i, IsOpen (U i)) → (⋃ i, U i = univ) →
      ∃ (β : Type) (_ : Countable β) (D : β → Set A),
        (∀ j, IsClopen (D j)) ∧ (⋃ j, D j = univ) ∧
          Pairwise (fun j k => Disjoint (D j) (D k)) ∧ LocallyFinite D ∧
            ∀ j, ∃ i, D j ⊆ U i

def paracompact_subspaces : Prop := ∀ A : Set ℝₗ, ParacompactSpace A

def paracompact_line : Prop := ParacompactSpace ℝₗ

def plane_not_lindelof : Prop := ¬ LindelofSpace (ℝₗ × ℝₗ)

def plane_not_paracompact : Prop := ¬ ParacompactSpace (ℝₗ × ℝₗ)

end SorgenfreyChallenge
