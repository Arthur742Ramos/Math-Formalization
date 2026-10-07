/-
Copyright (c) 2026 Arthur Freitas Ramos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos
-/
module

public import Boundary
public import Mathlib.Topology.MetricSpace.Closeds
public import Mathlib.Topology.UnitInterval

@[expose] public section

open Set Topology TopologicalSpace

namespace OrderArcs

/-- A proper subcontinuum of a compact Hausdorff continuum has a strict intermediate
subcontinuum. The proof uses boundary bumping in a closed neighborhood. -/
theorem exists_intermediate_univ {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] [ConnectedSpace X]
    {A : Set X} (hAc : IsCompact A) (hA : IsConnected A) (hproper : A ≠ univ) :
    ∃ D : Set X, IsCompact D ∧ IsConnected D ∧ A ⊂ D ∧ D ⊂ univ := by
  classical
  have hzex : ∃ z : X, z ∉ A := by
    by_contra h
    apply hproper
    apply eq_univ_iff_forall.mpr
    intro z
    by_contra hz
    exact h ⟨z, hz⟩
  obtain ⟨z, hz⟩ := hzex
  have hAZ : A ⊆ ({z} : Set X)ᶜ := by
    intro a ha
    simpa only [mem_compl_iff, mem_singleton_iff] using fun h : a = z => hz (h ▸ ha)
  obtain ⟨U, hU, hAU, hUZ⟩ := hAc.exists_isOpen_closure_subset
    (IsOpen.mem_nhdsSet isClosed_singleton.isOpen_compl |>.mpr hAZ)
  let F := closure U
  have hF : IsClosed F := isClosed_closure
  have hAF : A ⊆ F := hAU.trans subset_closure
  have hAI : A ⊆ interior F := hAU.trans (hU.subset_interior_iff.mpr subset_closure)
  have hzF : z ∉ F := by
    intro h
    exact (hUZ h) (mem_singleton z)
  have hFproper : F ≠ univ := by
    intro h
    exact hzF (h ▸ mem_univ z)
  obtain ⟨x, hx⟩ := hA.nonempty
  let D := connectedComponentIn F x
  have hAD : A ⊆ D := hA.isPreconnected.subset_connectedComponentIn hx hAF
  have hDF : D ⊆ F := connectedComponentIn_subset F x
  have hDcompact : IsCompact D := by
    have : CompactSpace F := isCompact_iff_compactSpace.mp hF.isCompact
    dsimp [D]
    rw [connectedComponentIn_eq_image (hAF hx)]
    exact isClosed_connectedComponent.isCompact.image continuous_subtype_val
  have hDconn : IsConnected D := isConnected_connectedComponentIn_iff.mpr (hAF hx)
  obtain ⟨y, hyD, hyFr⟩ := BoundaryBumping.closed_component_meets_frontier hF hFproper (hAF hx)
  have hyA : y ∉ A := by
    intro hy
    exact hyFr.2 (hAI hy)
  refine ⟨D, hDcompact, hDconn, ?_, ?_⟩
  · exact ssubset_iff_subset_ne.mpr ⟨hAD, fun h => hyA (h ▸ hyD)⟩
  · refine ssubset_iff_subset_ne.mpr ⟨subset_univ D, ?_⟩
    intro h
    exact hzF (hDF (h ▸ mem_univ z))

/-- Interpolation takes place in the larger continuum; the ambient space need
not be connected or compact. -/
theorem exists_intermediate {X : Type*} [TopologicalSpace X] [T2Space X]
    {A B : Set X} (hAc : IsCompact A) (hA : IsConnected A)
    (hBc : IsCompact B) (hB : IsConnected B) (hAB : A ⊂ B) :
    ∃ D : Set X, IsCompact D ∧ IsConnected D ∧ A ⊂ D ∧ D ⊂ B := by
  classical
  have : CompactSpace B := isCompact_iff_compactSpace.mp hBc
  have : ConnectedSpace B := Subtype.connectedSpace hB
  let A' : Set B := Subtype.val ⁻¹' A
  have hImage : Subtype.val '' A' = A := by
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr hAB.subset]
  have hAc' : IsCompact A' :=
    IsInducing.subtypeVal.isCompact_preimage' hAc (by simpa using hAB.subset)
  have hA' : IsConnected A' := by
    refine ⟨?_, IsInducing.subtypeVal.isPreconnected_image.mp ?_⟩
    · obtain ⟨a, ha⟩ := hA.nonempty
      exact ⟨⟨a, hAB.subset ha⟩, ha⟩
    · rw [hImage]
      exact hA.isPreconnected
  have hproper' : A' ≠ univ := by
    intro h
    apply hAB.ne
    refine Subset.antisymm hAB.subset ?_
    intro b hb
    have : (⟨b, hb⟩ : B) ∈ A' := h ▸ mem_univ _
    exact this
  obtain ⟨D', hDc, hD, hAD, hDU⟩ := exists_intermediate_univ hAc' hA' hproper'
  let D : Set X := Subtype.val '' D'
  have hADsub : A ⊆ D := by
    rw [← hImage]
    exact image_mono hAD.subset
  have hDBsub : D ⊆ B := by
    rintro _ ⟨b, _, rfl⟩
    exact b.property
  refine ⟨D, hDc.image continuous_subtype_val, hD.image _ continuous_subtype_val.continuousOn,
    ssubset_iff_subset_ne.mpr ⟨hADsub, ?_⟩, ssubset_iff_subset_ne.mpr ⟨hDBsub, ?_⟩⟩
  · intro h
    apply hAD.ne
    apply Subset.antisymm hAD.subset
    intro d hd
    change d.val ∈ A
    rw [h]
    exact ⟨d, hd, rfl⟩
  · intro h
    apply hDU.ne
    apply Subset.antisymm (subset_univ D')
    intro b _
    have hbD : b.val ∈ D := by
      rw [h]
      exact b.property
    obtain ⟨d, hd, heq⟩ := hbD
    have : d = b := Subtype.ext heq
    exact this ▸ hd

/-- A dense sequence detects strict inclusion through one distance coordinate. -/
theorem exists_infDist_strict {X : Type*} [MetricSpace X] (q : ℕ → X)
    (hq : DenseRange q) {K L : NonemptyCompacts X} (hKL : K < L) :
    ∃ n : ℕ, Metric.infDist (q n) (L : Set X) < Metric.infDist (q n) (K : Set X) := by
  classical
  have hex : ∃ z : X, z ∈ (L : Set X) ∧ z ∉ (K : Set X) := by
    by_contra h
    apply hKL.ne
    apply NonemptyCompacts.ext
    apply Subset.antisymm hKL.le
    intro z hz
    by_contra hzK
    exact h ⟨z, hz, hzK⟩
  obtain ⟨z, hzL, hzK⟩ := hex
  have hzpos : 0 < Metric.infDist z (K : Set X) :=
    (K.isCompact.isClosed.notMem_iff_infDist_pos K.nonempty).mp hzK
  have hzlt : Metric.infDist z (L : Set X) < Metric.infDist z (K : Set X) := by
    rw [Metric.infDist_zero_of_mem hzL]
    exact hzpos
  have hopen : IsOpen {x : X | Metric.infDist x (L : Set X) < Metric.infDist x (K : Set X)} :=
    isOpen_lt (Metric.lipschitz_infDist_pt _).continuous
      (Metric.lipschitz_infDist_pt _).continuous
  obtain ⟨n, hn⟩ := hq.exists_mem_open hopen ⟨z, hzlt⟩
  exact ⟨n, hn⟩

end OrderArcs

#print axioms OrderArcs.exists_intermediate_univ
#print axioms OrderArcs.exists_intermediate
#print axioms OrderArcs.exists_infDist_strict
