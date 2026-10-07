/-
Copyright (c) 2026 Arthur Freitas Ramos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos
-/
module

public import Mathlib.Topology.MetricSpace.Closeds
public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.Connected.PathConnected

@[expose] public section
open Set Topology TopologicalSpace
universe u
namespace Composants
variable {X : Type u} [tX : TopologicalSpace X]

def IsSubcontinuum (K : Set X) : Prop := IsCompact K ∧ IsConnected K

def IsIndecomposable (X : Type u) [tX : TopologicalSpace X] : Prop :=
  ∀ K L : Set X, IsSubcontinuum K → IsSubcontinuum L →
    K ∪ L = univ → K = univ ∨ L = univ

def composant (x : X) : Set X :=
  {y | ∃ K : Set X, IsSubcontinuum K ∧ K ≠ univ ∧ x ∈ K ∧ y ∈ K}

end Composants

namespace HyperspaceComponents
variable {X : Type*}

abbrev ProperContinuum (X : Type*) [tX : TopologicalSpace X] :=
  {K : NonemptyCompacts X // IsConnected (K : Set X) ∧ (K : Set X) ≠ univ}

section Union
variable [tX : TopologicalSpace X]

def familyUnion (γ : unitInterval → NonemptyCompacts X) (s : Set unitInterval) : Set X :=
  ⋃ (t : unitInterval) (_ht : t ∈ s), (γ t : Set X)

theorem proper_familyUnion [hT2 : T2Space X] (hi : Composants.IsIndecomposable X)
    (γ : unitInterval → NonemptyCompacts X) (hγ : Continuous γ)
    (hc : ∀ t, IsConnected (γ t : Set X))
    (hp : ∀ t, (γ t : Set X) ≠ univ) :
    Composants.IsSubcontinuum (familyUnion γ univ) ∧ familyUnion γ univ ≠ univ := by
  sorry

end Union

theorem joined_iff_common_continuum [mX : MetricSpace X] [cX : CompactSpace X]
    (hi : Composants.IsIndecomposable X) (A B : ProperContinuum X) :
    Joined A B ↔ ∃ K : ProperContinuum X, A.val ≤ K.val ∧ B.val ≤ K.val := by
  sorry

theorem joined_iff_same_composant [mX : MetricSpace X] [cX : CompactSpace X]
    (hi : Composants.IsIndecomposable X) (A B : ProperContinuum X) :
    Joined A B ↔ ∃ x : X,
      (A.val : Set X) ⊆ Composants.composant x ∧
      (B.val : Set X) ⊆ Composants.composant x := by
  sorry

theorem pathComponent_eq_composant [mX : MetricSpace X] [cX : CompactSpace X]
    (hi : Composants.IsIndecomposable X) (A : ProperContinuum X)
    {x : X} (hx : x ∈ (A.val : Set X)) :
    pathComponent A = {B : ProperContinuum X | (B.val : Set X) ⊆ Composants.composant x} := by
  sorry

theorem uncountably_many_path_components [mX : MetricSpace X] [cX : CompactSpace X]
    [ccX : ConnectedSpace X] [nX : Nontrivial X] (hi : Composants.IsIndecomposable X) :
    ¬ (Set.range (pathComponent : ProperContinuum X → Set (ProperContinuum X))).Countable := by
  sorry

theorem no_proper_continuum_of_subsingleton [tX : TopologicalSpace X] [ssX : Subsingleton X] :
    IsEmpty (ProperContinuum X) := by
  sorry

end HyperspaceComponents
