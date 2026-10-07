/-
Copyright (c) 2026 Arthur Freitas Ramos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos
-/
module
public import OrderArc
public import PathUnion
public import Mathlib.Topology.Connected.PathConnected

@[expose] public section
open Set Topology TopologicalSpace
namespace HyperspaceComponents
variable {X : Type*}

/-- The punctured hyperspace C(X) with its induced Vietoris topology. -/
abbrev ProperContinuum (X : Type*) [tX : TopologicalSpace X] :=
  {K : NonemptyCompacts X // IsConnected (K : Set X) ∧ (K : Set X) ≠ univ}

theorem proper_union [tX : TopologicalSpace X] (hi : Composants.IsIndecomposable X)
    {K L : Set X} (hK : Composants.IsSubcontinuum K)
    (hL : Composants.IsSubcontinuum L) (hpK : K ≠ univ) (hpL : L ≠ univ)
    (hKL : (K ∩ L).Nonempty) :
    Composants.IsSubcontinuum (K ∪ L) ∧ K ∪ L ≠ univ := by
  refine ⟨⟨hK.1.union hL.1, hK.2.union hKL hL.2⟩, ?_⟩
  intro he
  exact (hi K L hK hL he).elim hpK hpL

theorem exists_common_continuum_of_composant [tX : TopologicalSpace X]
    (hi : Composants.IsIndecomposable X)
    (A B : ProperContinuum X) (x : X)
    (hA : (A.val : Set X) ⊆ Composants.composant x)
    (hB : (B.val : Set X) ⊆ Composants.composant x) :
    ∃ K : ProperContinuum X, A.val ≤ K.val ∧ B.val ≤ K.val := by
  obtain ⟨a, ha⟩ := A.val.nonempty
  obtain ⟨b, hb⟩ := B.val.nonempty
  obtain ⟨M, hM, hpM, hxM, haM⟩ := hA ha
  obtain ⟨N, hN, hpN, hxN, hbN⟩ := hB hb
  have hAM := proper_union hi ⟨A.val.isCompact, A.property.1⟩ hM
    A.property.2 hpM ⟨a, ha, haM⟩
  have hAMN := proper_union hi hAM.1 hN hAM.2 hpN ⟨x, Or.inr hxM, hxN⟩
  have hD := proper_union hi hAMN.1 ⟨B.val.isCompact, B.property.1⟩
    hAMN.2 B.property.2 ⟨b, Or.inr hbN, hb⟩
  let K : NonemptyCompacts X := ⟨⟨_, hD.1.1⟩, hD.1.2.nonempty⟩
  exact ⟨⟨K, hD.1.2, hD.2⟩,
    fun y hy => Or.inl (Or.inl (Or.inl hy)), fun y hy => Or.inr hy⟩

theorem joined_of_le [mX : MetricSpace X] [cX : CompactSpace X]
    (A B : ProperContinuum X) (hAB : A.val ≤ B.val) : Joined A B := by
  classical
  by_cases he : A.val = B.val
  · have : A = B := Subtype.ext he
    subst B
    exact Joined.refl A
  obtain ⟨γ, hγ, -, hγ0, hγ1, hc, hm⟩ := OrderArcs.exists_order_arc
    A.val B.val A.property.1 B.property.1 (lt_of_le_of_ne hAB he)
  have hp : ∀ t, (γ t : Set X) ≠ univ := by
    intro t ht
    apply B.property.2
    apply subset_antisymm (subset_univ _)
    intro x _
    have hx : x ∈ (γ t : Set X) := ht ▸ mem_univ x
    have hs : γ t ≤ B.val := by simpa only [hγ1] using hm.monotone unitInterval.le_one'
    exact hs hx
  exact ⟨{
    toFun := fun t => ⟨γ t, hc t, hp t⟩
    continuous_toFun := hγ.subtype_mk _
    source' := Subtype.ext hγ0
    target' := Subtype.ext hγ1 }⟩

theorem joined_iff_common_continuum [mX : MetricSpace X] [cX : CompactSpace X]
    (hi : Composants.IsIndecomposable X) (A B : ProperContinuum X) :
    Joined A B ↔ ∃ K : ProperContinuum X, A.val ≤ K.val ∧ B.val ≤ K.val := by
  constructor
  · rintro ⟨γ⟩
    let f : unitInterval → NonemptyCompacts X := fun t => (γ t).val
    obtain ⟨hU, hpU⟩ := proper_familyUnion hi f
      (continuous_subtype_val.comp γ.continuous)
      (fun t => (γ t).property.1) (fun t => (γ t).property.2)
    let K : NonemptyCompacts X := ⟨⟨familyUnion f univ, hU.1⟩, hU.2.nonempty⟩
    refine ⟨⟨K, hU.2, hpU⟩, ?_, ?_⟩
    · change (A.val : Set X) ⊆ familyUnion f univ
      simpa only [f, γ.source] using subset_familyUnion f (mem_univ 0)
    · change (B.val : Set X) ⊆ familyUnion f univ
      simpa only [f, γ.target] using subset_familyUnion f (mem_univ 1)
  · rintro ⟨K, hAK, hBK⟩
    exact (joined_of_le A K hAK).trans (joined_of_le B K hBK).symm

theorem joined_iff_same_composant [mX : MetricSpace X] [cX : CompactSpace X]
    (hi : Composants.IsIndecomposable X) (A B : ProperContinuum X) :
    Joined A B ↔ ∃ x : X,
      (A.val : Set X) ⊆ Composants.composant x ∧
      (B.val : Set X) ⊆ Composants.composant x := by
  rw [joined_iff_common_continuum hi A B]
  constructor
  · rintro ⟨K, hAK, hBK⟩
    obtain ⟨x, hx⟩ := K.val.nonempty
    exact ⟨x, fun y hy => ⟨K.val, ⟨K.val.isCompact, K.property.1⟩,
      K.property.2, hx, hAK hy⟩,
      fun y hy => ⟨K.val, ⟨K.val.isCompact, K.property.1⟩, K.property.2, hx, hBK hy⟩⟩
  · rintro ⟨x, hA, hB⟩
    exact exists_common_continuum_of_composant hi A B x hA hB

theorem pathComponent_eq_composant [mX : MetricSpace X] [cX : CompactSpace X]
    (hi : Composants.IsIndecomposable X) (A : ProperContinuum X)
    {x : X} (hx : x ∈ (A.val : Set X)) :
    pathComponent A = {B : ProperContinuum X | (B.val : Set X) ⊆ Composants.composant x} := by
  ext B
  change Joined A B ↔ (B.val : Set X) ⊆ Composants.composant x
  constructor
  · intro h
    obtain ⟨K, hAK, hBK⟩ := (joined_iff_common_continuum hi A B).mp h
    exact fun y hy => ⟨K.val, ⟨K.val.isCompact, K.property.1⟩,
      K.property.2, hAK hx, hBK hy⟩
  · intro hB
    have hA : (A.val : Set X) ⊆ Composants.composant x := fun y hy =>
      ⟨A.val, ⟨A.val.isCompact, A.property.1⟩, A.property.2, hx, hy⟩
    exact (joined_iff_same_composant hi A B).mpr ⟨x, hA, hB⟩

def singletonContinuum [tX : TopologicalSpace X] [nX : Nontrivial X] (x : X) : ProperContinuum X :=
  ⟨{x}, isConnected_singleton, by
    change ({x} : Set X) ≠ univ
    obtain ⟨y, hy⟩ := exists_ne x
    intro he
    have : y ∈ ({x} : Set X) := he ▸ mem_univ y
    exact hy (mem_singleton_iff.mp this)⟩

theorem composant_eq_of_singleton_components_eq [mX : MetricSpace X] [cX : CompactSpace X]
    [nX : Nontrivial X] (hi : Composants.IsIndecomposable X) {x y : X}
    (h : pathComponent (singletonContinuum x) = pathComponent (singletonContinuum y)) :
    Composants.composant x = Composants.composant y := by
  have hxy : Joined (singletonContinuum x) (singletonContinuum y) := by
    change singletonContinuum y ∈ pathComponent (singletonContinuum x)
    rw [h]
    exact mem_pathComponent_self _
  obtain ⟨K, hxK, hyK⟩ := (joined_iff_common_continuum hi _ _).mp hxy
  have hyx : y ∈ Composants.composant x :=
    ⟨K.val, ⟨K.val.isCompact, K.property.1⟩, K.property.2,
      hxK (mem_singleton x), hyK (mem_singleton y)⟩
  rcases Composants.composants_eq_or_disjoint hi x y with he | hd
  · exact he
  · exact (Set.disjoint_left.mp hd hyx (Composants.mem_composant_self y)).elim

theorem uncountably_many_path_components [mX : MetricSpace X] [cX : CompactSpace X]
    [ccX : ConnectedSpace X] [nX : Nontrivial X] (hi : Composants.IsIndecomposable X) :
    ¬ (Set.range (pathComponent : ProperContinuum X → Set (ProperContinuum X))).Countable := by
  classical
  intro hc
  let f : X → Set (ProperContinuum X) := fun x => pathComponent (singletonContinuum x)
  let S : Set (Set (ProperContinuum X)) := Set.range f
  have hS : S.Countable := hc.mono (by rintro _ ⟨x, rfl⟩; exact ⟨singletonContinuum x, rfl⟩)
  let choosePoint : S → X := fun C => Classical.choose C.property
  let g : S → Set X := fun C => Composants.composant (choosePoint C)
  have hsub : Set.range (Composants.composant : X → Set X) ⊆ Set.range g := by
    rintro _ ⟨x, rfl⟩
    let C : S := ⟨f x, x, rfl⟩
    refine ⟨C, ?_⟩
    exact composant_eq_of_singleton_components_eq hi (Classical.choose_spec C.property)
  have : Countable S := hS.to_subtype
  exact Composants.uncountably_many_composants hi (Set.countable_range g |>.mono hsub)

theorem no_proper_continuum_of_subsingleton [tX : TopologicalSpace X] [ssX : Subsingleton X] :
    IsEmpty (ProperContinuum X) := by
  refine ⟨fun K => K.property.2 ?_⟩
  obtain ⟨x, hx⟩ := K.val.nonempty
  apply eq_univ_iff_forall.mpr
  intro y
  simpa only [Subsingleton.elim y x] using hx

end HyperspaceComponents

#print axioms HyperspaceComponents.joined_iff_same_composant
#print axioms HyperspaceComponents.pathComponent_eq_composant
#print axioms HyperspaceComponents.uncountably_many_path_components
