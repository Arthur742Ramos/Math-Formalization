/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz
-/
module

public import Sequences
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.Metrizable.Basic

/-!
# Normal products with compact metrizable spaces

Finite unions of members of a countable basis form countably many candidate
neighborhoods for compact fibers. Compactness makes the corresponding conditions
on the first coordinate open. A locally finite shrinking then separates the
two closed sets in the product. Only the compact factor needs regularity.
-/

@[expose] public section

open Set Filter TopologicalSpace
open scoped Topology

namespace Dowker

variable {X K : Type*} [TopologicalSpace X] [TopologicalSpace K]

abbrev ProductCandidate (K : Type*) [TopologicalSpace K] [SecondCountableTopology K] :=
  Finset (countableBasis K)

def candidateOpen [SecondCountableTopology K] (s : ProductCandidate K) : Set K :=
  ⋃ i ∈ s, (i : Set K)

theorem candidateOpen_isOpen [SecondCountableTopology K] (s : ProductCandidate K) :
    IsOpen (candidateOpen s) :=
  isOpen_iUnion fun i => isOpen_iUnion fun _ => isOpen_of_mem_countableBasis i.property

theorem exists_candidate [RegularSpace K] [SecondCountableTopology K]
    {A D : Set K} (hA : IsCompact A) (hD : IsClosed D) (hd : Disjoint A D) :
    ∃ s : ProductCandidate K, A ⊆ candidateOpen s ∧ closure (candidateOpen s) ⊆ Dᶜ := by
  classical
  let E : Set (countableBasis K) := {i | closure (i : Set K) ⊆ Dᶜ}
  have hcov : A ⊆ ⋃ i ∈ E, (i : Set K) := by
    intro y hy
    have hyD : y ∈ Dᶜ := fun hyD => Set.disjoint_left.mp hd hy hyD
    obtain ⟨i, hi, hyi, hiD⟩ :=
      (isBasis_countableBasis K).exists_closure_subset (hD.isOpen_compl.mem_nhds hyD)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, mem_iUnion.mpr ⟨hiD, hyi⟩⟩
  obtain ⟨E', hE', hEf, hAcov⟩ := hA.elim_finite_subcover_image
    (fun i _ => isOpen_of_mem_countableBasis i.property) hcov
  refine ⟨hEf.toFinset, ?_, ?_⟩
  · simpa only [candidateOpen, Set.Finite.mem_toFinset] using hAcov
  · intro y hy
    rw [candidateOpen, Finset.closure_biUnion] at hy
    obtain ⟨i, hi'⟩ := mem_iUnion.mp hy
    obtain ⟨hi, hyi⟩ := mem_iUnion.mp hi'
    have hiE : i ∈ E' := by simpa only [Set.Finite.mem_toFinset] using hi
    exact hE' hiE hyi

/-- A normal countably paracompact space has normal product with any compact,
regular, second-countable space. -/
theorem CountablyParacompact.normal_product [NormalSpace X] [CompactSpace K]
    [RegularSpace K] [SecondCountableTopology K] (hX : CountablyParacompact X) :
    NormalSpace (X × K) := by
  classical
  constructor
  intro A D hA hD hd
  let H : ProductCandidate K → Set K := candidateOpen
  let P : ProductCandidate K → Set X := fun s =>
    Prod.fst '' (A ∩ (univ ×ˢ (H s)ᶜ))
  let Q : ProductCandidate K → Set X := fun s =>
    Prod.fst '' (D ∩ (univ ×ˢ closure (H s)))
  let U : ProductCandidate K → Set X := fun s => (P s)ᶜ ∩ (Q s)ᶜ
  have hUo : ∀ s, IsOpen (U s) := by
    intro s
    exact (isClosedMap_fst_of_compactSpace _
      (hA.inter (isClosed_univ.prod (candidateOpen_isOpen s).isClosed_compl))).isOpen_compl.inter
      (isClosedMap_fst_of_compactSpace _
        (hD.inter (isClosed_univ.prod isClosed_closure))).isOpen_compl
  have hUc : (⋃ s, U s) = univ := by
    apply eq_univ_of_forall
    intro x
    have hc : Continuous (fun y : K => (x, y)) := continuous_const.prodMk continuous_id
    have hAx : IsCompact ((fun y => (x, y)) ⁻¹' A) := (hA.preimage hc).isCompact
    have hDx : IsClosed ((fun y => (x, y)) ⁻¹' D) := hD.preimage hc
    have hdx : Disjoint ((fun y => (x, y)) ⁻¹' A) ((fun y => (x, y)) ⁻¹' D) :=
      Set.disjoint_left.mpr fun y hyA hyD => Set.disjoint_left.mp hd hyA hyD
    obtain ⟨s, hsA, hsD⟩ := exists_candidate hAx hDx hdx
    refine mem_iUnion.mpr ⟨s, ?_, ?_⟩
    · rintro ⟨p, hp, hpx⟩
      exact hp.2.2 (hsA (by simpa [← hpx] using hp.1))
    · rintro ⟨p, hp, hpx⟩
      exact hsD hp.2.2 (by simpa [← hpx] using hp.1)
  obtain ⟨V, hVo, hVc, hVf, hVU⟩ := hX.precise_refinement U hUo hUc
  obtain ⟨W, hWc, hWo, hWV⟩ := exists_iUnion_eq_closure_subset hVo hVf.point_finite hVc
  have hWf : LocallyFinite W := hVf.subset fun s => subset_closure.trans (hWV s)
  let S : Set (X × K) := ⋃ s, W s ×ˢ H s
  have hSo : IsOpen S := isOpen_iUnion fun s => (hWo s).prod (candidateOpen_isOpen s)
  have hAS : A ⊆ S := by
    intro p hp
    obtain ⟨s, hs⟩ := mem_iUnion.mp (hWc.symm ▸ mem_univ p.1)
    refine mem_iUnion.mpr ⟨s, hs, ?_⟩
    have hpU : p.1 ∈ U s := hVU s (hWV s (subset_closure hs))
    by_contra hpH
    exact hpU.1 ⟨p, ⟨hp, mem_univ p.1, hpH⟩, rfl⟩
  have hSD : Disjoint (closure S) D := by
    apply Set.disjoint_left.mpr
    intro p hp hpD
    rw [hWf.prod_right H |>.closure_iUnion] at hp
    obtain ⟨s, hs⟩ := mem_iUnion.mp hp
    rw [closure_prod_eq] at hs
    have hpU : p.1 ∈ U s := hVU s (hWV s hs.1)
    exact hpU.2 ⟨p, ⟨hpD, mem_univ p.1, hs.2⟩, rfl⟩
  refine ⟨S, (closure S)ᶜ, hSo, isClosed_closure.isOpen_compl, hAS, ?_, ?_⟩
  · intro p hpD hpS
    exact Set.disjoint_left.mp hSD hpS hpD
  · exact Set.disjoint_left.mpr fun p hpS hpC => hpC (subset_closure hpS)

/-- Dowker's compact metrizable product theorem; no separation condition is
imposed on the first factor beyond normality. -/
theorem CountablyParacompact.normal_compact_metrizable_product [NormalSpace X]
    [CompactSpace K] [MetrizableSpace K] (hX : CountablyParacompact X) :
    NormalSpace (X × K) := hX.normal_product

end Dowker
