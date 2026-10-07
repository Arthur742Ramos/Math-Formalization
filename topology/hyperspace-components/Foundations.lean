/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz
-/
module

public import Boundary
public import Interior
public import Mathlib.Topology.Baire.LocallyCompactRegular

/-! Composants of continua, following Sturm (2009), Theorems 1.8, 1.10, 1.11 and 1.13.
The ambient type is the continuum itself. The literal definition excludes the whole space.
The support modules retain the complete pinned proofs credited in PROVENANCE.md. -/

@[expose] public section
open Set Topology TopologicalSpace
universe u
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
  refine ⟨{x}, ⟨isCompact_singleton, isConnected_singleton⟩, ?_, by simp, by simp⟩
  obtain ⟨y, hy⟩ := exists_ne x
  intro he
  have : y ∈ ({x} : Set X) := he ▸ mem_univ y
  exact hy (mem_singleton_iff.mp this)

/-- Every composant of a nondegenerate compact Hausdorff continuum is dense. -/
theorem dense_composant [cX : CompactSpace X] [hX : T2Space X] [cnX : ConnectedSpace X]
    [ntX : Nontrivial X] (x : X) : Dense (composant x) := by
  rw [dense_iff_inter_open]
  intro U hU hnU
  by_cases hxU : x ∈ U
  · exact ⟨x, hxU, mem_composant_self x⟩
  obtain ⟨y, hy⟩ := hnU
  obtain ⟨V, hV, hyV, hVU⟩ := isTopologicalBasis_opens.exists_closure_subset (hU.mem_nhds hy)
  have hxF : x ∈ Vᶜ := fun hxV => hxU (hVU (subset_closure hxV))
  have hp : Vᶜ ≠ (univ : Set X) := by
    intro he
    exact (show y ∈ Vᶜ from he ▸ mem_univ y) hyV
  obtain ⟨K, hKc, hKn, hxK, hKF, z, hzK, hzFr⟩ :=
    BoundaryBumping.exists_subcontinuum_meeting_frontier hV.isClosed_compl hp hxF
  refine ⟨z, ?_, ⟨K, ⟨hKc, hKn⟩, ?_, hxK, hzK⟩⟩
  · rw [frontier_compl] at hzFr
    exact hVU (frontier_subset_closure hzFr)
  · intro he
    exact hp (subset_antisymm (subset_univ _) (he ▸ hKF))

/-- Each composant is connected, even without indecomposability. -/
theorem isConnected_composant [ntX : Nontrivial X] (x : X) : IsConnected (composant x) := by
  refine ⟨⟨x, mem_composant_self x⟩, ?_⟩
  have he : composant x = ⋃ K : {K : Set X // IsSubcontinuum K ∧ K ≠ univ ∧ x ∈ K},
      (K : Set X) := by
    ext y
    simp only [composant, mem_ofPred_eq, mem_iUnion, Subtype.exists, exists_prop]
    tauto
  rw [he]
  exact isPreconnected_iUnion ⟨x, mem_iInter.mpr (fun K => K.2.2.2)⟩
    (fun K => K.2.1.2.isPreconnected)

private theorem mem_trans (hi : IsIndecomposable X) {x y z : X}
    (hxy : y ∈ composant x) (hyz : z ∈ composant y) : z ∈ composant x := by
  obtain ⟨K, hK, hpK, hxK, hyK⟩ := hxy
  obtain ⟨L, hL, hpL, hyL, hzL⟩ := hyz
  refine ⟨K ∪ L, ⟨hK.1.union hL.1, hK.2.union ⟨y, hyK, hyL⟩ hL.2⟩, ?_,
    Or.inl hxK, Or.inr hzL⟩
  intro hc
  exact (hi K L hK hL hc).elim hpK hpL

private theorem mem_symm {x y : X} (hxy : y ∈ composant x) : x ∈ composant y := by
  obtain ⟨K, hK, hp, hx, hy⟩ := hxy
  exact ⟨K, hK, hp, hy, hx⟩

/-- In an indecomposable continuum, composants are equal or disjoint. -/
theorem composants_eq_or_disjoint (hi : IsIndecomposable X) (x y : X) :
    composant x = composant y ∨ Disjoint (composant x) (composant y) := by
  classical
  rcases disjoint_or_nonempty_inter (composant x) (composant y) with hd | ⟨z, hxz, hyz⟩
  · exact Or.inr hd
  · left
    have hxy := mem_trans hi hxz (mem_symm hyz)
    have hyx := mem_symm hxy
    exact subset_antisymm (fun _ h => mem_trans hi hyx h) (fun _ h => mem_trans hi hxy h)

/-- The composants cover every point of a nondegenerate continuum. -/
theorem iUnion_composant [ntX : Nontrivial X] : (⋃ x : X, composant x) = univ := by
  apply subset_antisymm (subset_univ _)
  intro x _
  exact mem_iUnion.mpr ⟨x, mem_composant_self x⟩

private theorem component_subcontinuum [cX : CompactSpace X] [_hX : T2Space X]
    {U : Set X} (hU : IsOpen U) {x : X} (hx : x ∉ U) :
    IsSubcontinuum (connectedComponentIn Uᶜ x) := by
  have : CompactSpace (Uᶜ : Set X) := isCompact_iff_compactSpace.mp hU.isClosed_compl.isCompact
  refine ⟨?_, isConnected_connectedComponentIn_iff.mpr hx⟩
  rw [connectedComponentIn_eq_image hx]
  exact isClosed_connectedComponent.isCompact.image continuous_subtype_val

/-- Second countability gives a countable family of proper subcontinua whose union is a composant. -/
theorem composant_countable_union [cX : CompactSpace X] [hX : T2Space X] [scX : SecondCountableTopology X]
    (x : X) : ∃ S : Set (Set X), S.Countable ∧
      (∀ K ∈ S, IsSubcontinuum K ∧ K ≠ univ ∧ x ∈ K) ∧ composant x = ⋃₀ S := by
  classical
  let B : Set (Set X) := {U ∈ countableBasis X | x ∉ U}
  let C : Set X → Set X := fun U => connectedComponentIn Uᶜ x
  have hcB : B.Countable := (countable_countableBasis X).mono (fun _ h => h.1)
  have hC : ∀ U ∈ B, IsSubcontinuum (C U) ∧ C U ≠ univ ∧ x ∈ C U := by
    intro U hUB
    refine ⟨component_subcontinuum (isOpen_of_mem_countableBasis hUB.1) hUB.2, ?_,
      mem_connectedComponentIn hUB.2⟩
    obtain ⟨y, hy⟩ := nonempty_of_mem_countableBasis hUB.1
    intro he
    have hyC : y ∈ C U := he ▸ mem_univ y
    exact (connectedComponentIn_subset Uᶜ x hyC) hy
  refine ⟨C '' B, hcB.image C, ?_, ?_⟩
  · rintro _ ⟨U, hU, rfl⟩
    exact hC U hU
  · ext y
    constructor
    · rintro ⟨K, hK, hpK, hxK, hyK⟩
      have hn : Kᶜ.Nonempty := by
        by_contra h
        have he := congrArg (fun s : Set X => sᶜ) (not_nonempty_iff_eq_empty.mp h)
        exact hpK (by simpa using he)
      obtain ⟨U, hUB, hnU, hUK⟩ := (isBasis_countableBasis X).exists_nonempty_subset hn hK.1.isClosed.isOpen_compl
      have hKU : K ⊆ Uᶜ := fun z hz hzU => hUK hzU hz
      have hxU : x ∉ U := hKU hxK
      exact mem_sUnion.mpr ⟨C U, ⟨U, ⟨hUB, hxU⟩, rfl⟩,
        hK.2.isPreconnected.subset_connectedComponentIn hxK hKU hyK⟩
    · rintro ⟨K, ⟨U, hU, rfl⟩, hy⟩
      exact ⟨C U, (hC U hU).1, (hC U hU).2.1, (hC U hU).2.2, hy⟩

/-- Every composant of a second-countable indecomposable continuum is meagre. -/
theorem isMeagre_composant [cX : CompactSpace X] [hX : T2Space X] [cnX : ConnectedSpace X]
    [scX : SecondCountableTopology X] (hi : IsIndecomposable X) (x : X) : IsMeagre (composant x) := by
  obtain ⟨S, hcS, hS, he⟩ := composant_countable_union x
  rw [he, sUnion_eq_biUnion]
  apply isMeagre_biUnion hcS
  intro K hK
  exact ((IndecomposableContinuum.indecomposable_iff_nowhere_dense.mp hi)
    K (hS K hK).1 (hS K hK).2.1).isMeagre

/-- A nondegenerate second-countable indecomposable continuum has uncountably many distinct composants. -/
theorem uncountably_many_composants [cX : CompactSpace X] [hX : T2Space X] [cnX : ConnectedSpace X]
    [ntX : Nontrivial X] [scX : SecondCountableTopology X] (hi : IsIndecomposable X) :
    ¬ (Set.range (composant : X → Set X)).Countable := by
  intro hc
  have hm : IsMeagre (⋃ K ∈ Set.range (composant : X → Set X), K) := by
    apply isMeagre_biUnion hc
    rintro K ⟨x, rfl⟩
    exact isMeagre_composant hi x
  have he : (⋃ K ∈ Set.range (composant : X → Set X), K) = univ := by
    rw [biUnion_range, iUnion_composant]
  rw [he] at hm
  exact not_isMeagre_of_isOpen isOpen_univ Set.univ_nonempty hm

end Composants
