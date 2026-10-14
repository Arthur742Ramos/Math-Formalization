/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz
-/
module
public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.Compactness.LocallyFinite

/-!
# Perfect surjections and paracompactness

The principal claim is `paracompact_iff`: a continuous closed surjection from
a Hausdorff space with compact fibres preserves and reflects ordinary
open-cover paracompactness. This is the classical perfect-map invariant
theorem, as stated in Munkres, *Topology*, second edition, section 41,
exercise 8. It imposes no metric, countability, or local compactness hypothesis.

The inverse-image direction `paracompact_preimage` works without separation or
surjectivity. The image direction `paracompact_image` only needs regularity of
the target. `locallyFinite_image` supplies the compact-fibre transfer of indexed
families, and `paracompact_iff_refinements` is the regular-space locally finite
refinement criterion (Sakai, chapter 2, Theorem 2.6.3(a),(e)).

All notions in the selected statements are ordinary Mathlib notions. There
are no project-specific definitions, proof holes, or added axioms. The source
is a proof-bearing statement file to make the complete mathematical contract
independent of project imports. Comparator checks the separate Solution.
-/

public section
open Set Filter Function Topology
universe u v w
namespace PerfectParacompact
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- Closedness turns a fibre-containing open set into a neighbourhood in the target. -/
theorem fibre_neighbourhood {f : X → Y} (hc : IsClosedMap f) {y : Y}
    {U : Set X} (ho : IsOpen U) (hs : f ⁻¹' {y} ⊆ U) :
    ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧ f ⁻¹' V ⊆ U := by
  refine ⟨(f '' Uᶜ)ᶜ, (hc _ ho.isClosed_compl).isOpen_compl, ?_, ?_⟩
  · rintro ⟨x, hx, hxy⟩
    exact hx (hs (by simpa using hxy))
  · intro x hx
    by_contra h
    exact hx ⟨x, h, rfl⟩

/-- Perfect maps send arbitrary locally finite indexed families to locally finite families. -/
theorem locallyFinite_image {ι : Type w} {f : X → Y} (hc : IsClosedMap f)
    (hk : ∀ y, IsCompact (f ⁻¹' {y})) {C : ι → Set X} (hC : LocallyFinite C) :
    LocallyFinite (fun i => f '' C i) := by
  classical
  intro y
  choose U hUx hUf using fun x => hC.exists_mem_basis (nhds_basis_opens x)
  rcases (hk y).elim_finite_subcover U (fun x => (hUx x).2)
      (fun x _ => mem_iUnion.mpr ⟨x, (hUx x).1⟩) with ⟨T, hT⟩
  rcases fibre_neighbourhood hc (isOpen_iUnion fun x => isOpen_iUnion fun _ => (hUx x).2) hT
      with ⟨V, hVo, hyV, hVU⟩
  refine ⟨V, hVo.mem_nhds hyV, (T.finite_toSet.biUnion fun x _ => hUf x).subset ?_⟩
  rintro i ⟨z, ⟨x, hxC, rfl⟩, hxV⟩
  rcases mem_iUnion₂.mp (hVU hxV) with ⟨a, ha, hxa⟩
  exact mem_iUnion₂.mpr ⟨a, ha, x, hxC, hxa⟩

/-- A continuous closed map with compact fibres pulls paracompactness back.
Neither surjectivity nor separation hypotheses are needed. -/
theorem paracompact_preimage {f : X → Y} (hf : Continuous f) (hc : IsClosedMap f)
    (hk : ∀ y, IsCompact (f ⁻¹' {y})) [ParacompactSpace Y] : ParacompactSpace X := by
  classical
  constructor
  intro ι S hSo hS
  have hfinite : ∀ y : Y, ∃ T : Finset ι, f ⁻¹' {y} ⊆ ⋃ i ∈ T, S i :=
    fun y => (hk y).elim_finite_subcover S hSo (by rw [hS]; exact subset_univ _)
  choose T hT using hfinite
  choose V hVo hyV hVS using fun y => fibre_neighbourhood hc
    (isOpen_iUnion fun i => isOpen_iUnion fun _ => hSo i) (hT y)
  rcases precise_refinement V hVo (iUnion_eq_univ_iff.mpr fun y => ⟨y, hyV y⟩)
      with ⟨W, hWo, hW, hWf, hWV⟩
  let R : (Σ y : Y, ↥(T y)) → Set X := fun a => S a.2 ∩ f ⁻¹' W a.1
  have hRo : ∀ a, IsOpen (R a) := fun a => (hSo _).inter ((hWo _).preimage hf)
  have hR : ⋃ a, R a = univ := by
    apply iUnion_eq_univ_iff.mpr
    intro x
    rcases iUnion_eq_univ_iff.mp hW (f x) with ⟨y, hy⟩
    rcases mem_iUnion₂.mp (hVS y (hWV y hy)) with ⟨i, hi, hxi⟩
    exact ⟨⟨y, i, hi⟩, hxi, hy⟩
  have hRf : LocallyFinite R := by
    intro x
    rcases hWf (f x) with ⟨N, hN, hNf⟩
    refine ⟨f ⁻¹' N, hf.continuousAt hN,
      (hNf.biUnion fun y _ => finite_range (Sigma.mk y)).subset ?_⟩
    rintro ⟨y, i⟩ ⟨z, ⟨_, hzW⟩, hzN⟩
    exact mem_iUnion₂.mpr ⟨y, ⟨f z, hzW, hzN⟩, mem_range_self i⟩
  refine ⟨range R, Subtype.val, forall_subtype_range_iff.mpr hRo, ?_, hRf.on_range, ?_⟩
  · simpa only [iUnion_subtype, biUnion_range] using hR
  · exact forall_subtype_range_iff.mpr fun a => ⟨a.2, inter_subset_left⟩

/-- In a regular space, locally finite refinements need not initially be open.
Two refinements produce a locally finite open expansion of the first one. -/
theorem paracompact_of_refinements [RegularSpace Y]
    (H : ∀ (ι : Type v) (S : ι → Set Y), (∀ i, IsOpen (S i)) → (⋃ i, S i = univ) →
      ∃ (κ : Type v) (C : κ → Set Y), (⋃ i, C i = univ) ∧ LocallyFinite C ∧
        ∀ i, ∃ j, C i ⊆ S j) : ParacompactSpace Y := by
  classical
  constructor
  intro ι S hSo hS
  rcases H ι S hSo hS with ⟨κ, C, hC, hCf, hCS⟩
  choose a ha using hCS
  choose W hxW hWf using hCf
  choose R hRx hRW using fun x => (hasBasis_opens_closure x).mem_iff.mp (hxW x)
  rcases H Y R (fun x => (hRx x).2) (iUnion_eq_univ_iff.mpr fun x => ⟨x, (hRx x).1⟩)
      with ⟨γ, B, hB, hBf, hBR⟩
  choose b hb using hBR
  let D : γ → Set Y := fun j => closure (B j)
  have hDf : LocallyFinite D := hBf.closure
  have hDW : ∀ j, D j ⊆ W (b j) := fun j => (closure_mono (hb j)).trans (hRW _)
  let V : κ → Set Y := fun i => S (a i) ∩ (⋃ (j : γ) (_ : ¬ (C i ∩ W (b j)).Nonempty), D j)ᶜ
  have hVo : ∀ i, IsOpen (V i) := by
    intro i
    have hclosed : IsClosed (⋃ (j : γ) (_ : ¬ (C i ∩ W (b j)).Nonempty), D j) := by
      simpa only [iUnion_subtype, Function.comp_apply] using
        (hDf.comp_injective (Subtype.val_injective (p := fun j => ¬ (C i ∩ W (b j)).Nonempty))).isClosed_iUnion
          (fun j => isClosed_closure)
    exact (hSo _).inter hclosed.isOpen_compl
  have hCV : ∀ i, C i ⊆ V i := by
    intro i x hx
    refine ⟨ha i hx, ?_⟩
    rintro hxD
    rcases mem_iUnion₂.mp hxD with ⟨j, hj, hxD⟩
    exact hj ⟨x, hx, hDW j hxD⟩
  have hVf : LocallyFinite V := by
    intro x
    refine ⟨⋂ (j : γ) (_ : x ∉ D j), (D j)ᶜ,
      hDf.iInter_compl_mem_nhds (fun j => isClosed_closure) x,
      ((hDf.point_finite x).biUnion fun j _ => hWf (b j)).subset ?_⟩
    rintro i ⟨z, hzV, hzN⟩
    rcases iUnion_eq_univ_iff.mp hB z with ⟨j, hzB⟩
    have hzD : z ∈ D j := subset_closure hzB
    have hxD : x ∈ D j := by
      by_contra h
      exact (mem_iInter₂.mp hzN j h) hzD
    have hi : (C i ∩ W (b j)).Nonempty := by
      by_contra h
      exact hzV.2 (mem_iUnion₂.mpr ⟨j, h, hzD⟩)
    exact mem_iUnion₂.mpr ⟨j, hxD, hi⟩
  refine ⟨κ, V, hVo, ?_, hVf, fun i => ⟨a i, inter_subset_left⟩⟩
  apply iUnion_eq_univ_iff.mpr
  intro x
  rcases iUnion_eq_univ_iff.mp hC x with ⟨i, hi⟩
  exact ⟨i, hCV i hi⟩

/-- The regular-space locally finite refinement criterion, in both directions. -/
theorem paracompact_iff_refinements [RegularSpace Y] : ParacompactSpace Y ↔
    ∀ (ι : Type v) (S : ι → Set Y), (∀ i, IsOpen (S i)) → (⋃ i, S i = univ) →
      ∃ (κ : Type v) (C : κ → Set Y), (⋃ i, C i = univ) ∧ LocallyFinite C ∧
        ∀ i, ∃ j, C i ⊆ S j := by
  constructor
  · intro h ι S ho hS
    let _ := h
    rcases ParacompactSpace.locallyFinite_refinement ι S ho hS
      with ⟨κ, C, _, hC, hCf, hCS⟩
    exact ⟨κ, C, hC, hCf, hCS⟩
  · exact paracompact_of_refinements

/-- A closed continuous surjection takes normality to normality. -/
theorem normal_image {f : X → Y} (hf : Continuous f) (hc : IsClosedMap f)
    (hs : Surjective f) [NormalSpace X] : NormalSpace Y := by
  constructor
  intro A B hA hB hAB
  have hab : Disjoint (f ⁻¹' A) (f ⁻¹' B) := hAB.preimage f
  rcases normal_separation (hA.preimage hf) (hB.preimage hf) hab
      with ⟨U, V, hUo, hVo, hAU, hBV, hUV⟩
  refine ⟨(f '' Uᶜ)ᶜ, (f '' Vᶜ)ᶜ,
    (hc _ hUo.isClosed_compl).isOpen_compl,
    (hc _ hVo.isClosed_compl).isOpen_compl, ?_, ?_, ?_⟩
  · rintro y hy ⟨x, hx, rfl⟩
    exact hx (hAU hy)
  · rintro y hy ⟨x, hx, rfl⟩
    exact hx (hBV hy)
  · apply disjoint_left.mpr
    intro y hyU hyV
    rcases hs y with ⟨x, rfl⟩
    have hxU : x ∈ U := by
      by_contra h
      exact hyU ⟨x, h, rfl⟩
    have hxV : x ∈ V := by
      by_contra h
      exact hyV ⟨x, h, rfl⟩
    exact hUV.le_bot ⟨hxU, hxV⟩

/-- A perfect surjection sends paracompactness to a regular target. -/
theorem paracompact_image [RegularSpace Y] {f : X → Y} (hf : Continuous f)
    (hc : IsClosedMap f) (hk : ∀ y, IsCompact (f ⁻¹' {y}))
    (hs : Surjective f) [ParacompactSpace X] : ParacompactSpace Y := by
  apply paracompact_of_refinements
  intro ι S hSo hS
  have hp : ⋃ i, f ⁻¹' S i = univ := by
    rw [← preimage_iUnion, hS, preimage_univ]
  rcases precise_refinement (fun i => f ⁻¹' S i) (fun i => (hSo i).preimage hf) hp
      with ⟨C, hCo, hC, hCf, hCS⟩
  refine ⟨ι, fun i => f '' C i, ?_, locallyFinite_image hc hk hCf, fun i => ⟨i, ?_⟩⟩
  · apply iUnion_eq_univ_iff.mpr
    intro y
    rcases hs y with ⟨x, rfl⟩
    rcases iUnion_eq_univ_iff.mp hC x with ⟨i, hi⟩
    exact ⟨i, x, hi, rfl⟩
  · rintro y ⟨x, hx, rfl⟩
    exact hCS i hx

/-- A perfect surjection from a Hausdorff space preserves and reflects paracompactness.
No separation hypothesis is imposed on the target. -/
theorem paracompact_iff [T2Space X] {f : X → Y} (hf : Continuous f)
    (hc : IsClosedMap f) (hk : ∀ y, IsCompact (f ⁻¹' {y})) (hs : Surjective f) :
    ParacompactSpace X ↔ ParacompactSpace Y := by
  constructor
  · intro h
    let _ := h
    let _ : T1Space Y := ⟨fun y => by
      rcases hs y with ⟨x, rfl⟩
      simpa only [image_singleton] using hc {x} isClosed_singleton⟩
    let _ : NormalSpace Y := normal_image hf hc hs
    exact paracompact_image hf hc hk hs
  · intro h
    let _ := h
    exact paracompact_preimage hf hc hk

/-- The perfect image of a paracompact Hausdorff space is paracompact Hausdorff.
The codomain has no assumed separation property. -/
theorem paracompact_t2_image [T2Space X] {f : X → Y} (hf : Continuous f)
    (hc : IsClosedMap f) (hk : ∀ y, IsCompact (f ⁻¹' {y})) (hs : Surjective f)
    [ParacompactSpace X] : ParacompactSpace Y ∧ T2Space Y := by
  let _ : T1Space Y := ⟨fun y => by
    rcases hs y with ⟨x, rfl⟩
    simpa only [image_singleton] using hc {x} isClosed_singleton⟩
  let _ : NormalSpace Y := normal_image hf hc hs
  exact ⟨paracompact_image hf hc hk hs, inferInstance⟩

end PerfectParacompact
