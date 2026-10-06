/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz
-/
module
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.Baire.LocallyCompactRegular
public import Mathlib.Topology.GDelta.Basic
public import Mathlib.Topology.Sets.VietorisTopology
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Thickening
@[expose] public section
open Set Topology TopologicalSpace
universe u v
namespace Composants
variable {X : Type u} [tX : TopologicalSpace X]
/-- A nonempty compact connected subset. -/
def IsSubcontinuum (K : Set X) : Prop := IsCompact K ∧ IsConnected K
/-- No two proper subcontinua cover the ambient space. -/
def IsIndecomposable (X : Type u) [tX : TopologicalSpace X] : Prop :=
  ∀ K L : Set X, IsSubcontinuum K → IsSubcontinuum L →
    K ∪ L = univ → K = univ ∨ L = univ
/-- The union of all proper subcontinua containing x, with no extra point adjoined. -/
def composant (x : X) : Set X :=
  {y | ∃ K : Set X, IsSubcontinuum K ∧ K ≠ univ ∧ x ∈ K ∧ y ∈ K}
theorem mem_composant_self [ntX : Nontrivial X] (x : X) : x ∈ composant x := by
  sorry
theorem dense_composant [cX : CompactSpace X] [hX : T2Space X] [cnX : ConnectedSpace X]
    [ntX : Nontrivial X] (x : X) : Dense (composant x) := by
  sorry
theorem isConnected_composant [ntX : Nontrivial X] (x : X) : IsConnected (composant x) := by
  sorry
theorem composants_eq_or_disjoint (hi : IsIndecomposable X) (x y : X) :
    composant x = composant y ∨ @Disjoint (Set X)
      ((@Set.instCompleteAtomicBooleanAlgebra X).toCompleteBooleanAlgebra.toCompleteLattice.toConditionallyCompleteLattice.toConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup.toPartialOrder)
      _ (composant x) (composant y) := by
  sorry
theorem iUnion_composant [ntX : Nontrivial X] : (⋃ x : X, composant x) = univ := by
  sorry
theorem composant_countable_union [cX : CompactSpace X] [hX : T2Space X] [scX : SecondCountableTopology X]
    (x : X) : ∃ S : Set (Set X), S.Countable ∧
      (∀ K ∈ S, IsSubcontinuum K ∧ K ≠ univ ∧ x ∈ K) ∧ composant x = ⋃₀ S := by
  sorry
theorem isMeagre_composant [cX : CompactSpace X] [hX : T2Space X] [cnX : ConnectedSpace X]
    [scX : SecondCountableTopology X] (hi : IsIndecomposable X) (x : X) : IsMeagre (composant x) := by
  sorry
theorem uncountably_many_composants [cX : CompactSpace X] [hX : T2Space X] [cnX : ConnectedSpace X]
    [ntX : Nontrivial X] [scX : SecondCountableTopology X] (hi : IsIndecomposable X) :
    ¬ (Set.range (composant : X → Set X)).Countable := by
  sorry
end Composants
namespace Composants
variable {X : Type u} [tX : TopologicalSpace X]
/-- An open cover of the whole space, represented as a family of sets. -/
def IsOpenCover (ω : Set (Set X)) : Prop :=
  (∀ U ∈ ω, IsOpen U) ∧ ⋃₀ ω = univ
/-- A closed separator whose complementary open sides contain `A` and `B`. -/
def IsPartitionBetween (P A B : Set X) : Prop :=
  IsClosed P ∧ ∃ U V : Set X,
    IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧ U ∪ V = Pᶜ ∧ A ⊆ U ∧ B ⊆ V
/-- The inverse images of an open target cover refine the ambient cover on `P`. -/
def IsOmegaMap (ω : Set (Set X)) {P : Set X} {Y : Type v} [_tY : TopologicalSpace Y]
    (f : P → Y) : Prop :=
  Continuous f ∧ ∃ γ : Set (Set Y), IsOpenCover γ ∧
    ∀ V ∈ γ, ∃ U ∈ ω, f ⁻¹' V ⊆ Subtype.val ⁻¹' U
/-- A continuum is nonempty, compact, connected, and Hausdorff. -/
def IsContinuum (Y : Type v) [_tY : TopologicalSpace Y] : Prop :=
  Nonempty Y ∧ CompactSpace Y ∧ ConnectedSpace Y ∧ T2Space Y
end Composants
namespace Composants
variable {X : Type u} [mX : MetricSpace X]
theorem alexandroff_continua [cX : CompactSpace X] [cnX : ConnectedSpace X]
    (hi : IsIndecomposable X) (A B : Set X) (_hA : IsClosed A) (_hB : IsClosed B)
    (hdis : Disjoint A B) (ha : (interior A).Nonempty) (hb : (interior B).Nonempty) :
    ∃ ω : Set (Set X), IsOpenCover ω ∧ ∀ P : Set X, IsPartitionBetween P A B →
      ∀ (Y : Type v) [_tY : TopologicalSpace Y], IsContinuum Y →
        ∀ f : P → Y, Continuous f → Function.Surjective f → ¬ IsOmegaMap ω f := by
  sorry
end Composants
