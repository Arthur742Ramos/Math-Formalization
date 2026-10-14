/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz
-/
module

public import Sequences
public import Thresholds

/-!
# Countable paracompactness from normality of the interval product

A decreasing closed sequence with empty intersection is locally finite.
Placing its members at positive levels converging to zero therefore produces
a closed set disjoint from the zero slice. Normal separation gives the open
expansions required by the closed-sequence characterization.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace Dowker

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem normal_space_of_normal_product [Nonempty Y] [NormalSpace (X × Y)] :
    NormalSpace X := by
  classical
  let y : Y := Classical.choice inferInstance
  have hc : Continuous (fun x : X => (x, y)) := continuous_id.prodMk continuous_const
  constructor
  intro A B hA hB hd
  have hdp : Disjoint (A ×ˢ (univ : Set Y)) (B ×ˢ (univ : Set Y)) :=
    Set.disjoint_left.mpr fun _ ha hb => Set.disjoint_left.mp hd ha.1 hb.1
  obtain ⟨U, V, hUo, hVo, hAU, hBV, hUV⟩ :=
    normal_separation (hA.prod isClosed_univ) (hB.prod isClosed_univ) hdp
  refine ⟨(fun x => (x, y)) ⁻¹' U, (fun x => (x, y)) ⁻¹' V,
    hUo.preimage hc, hVo.preimage hc, ?_, ?_, ?_⟩
  · intro x hx
    exact hAU ⟨hx, mem_univ y⟩
  · intro x hx
    exact hBV ⟨hx, mem_univ y⟩
  · exact Set.disjoint_left.mpr fun x hx hy => Set.disjoint_left.mp hUV hx hy

theorem locallyFinite_of_antitone_closed_empty_intersection
    (F : ℕ → Set X) (hFc : ∀ n, IsClosed (F n)) (hFa : Antitone F)
    (hFe : (⋂ n, F n) = ∅) : LocallyFinite F := by
  intro x
  have he : ∃ n, x ∉ F n := by
    by_contra! hx
    have hmem : x ∈ ⋂ n, F n := mem_iInter.mpr hx
    rw [hFe] at hmem
    exact hmem
  obtain ⟨n, hn⟩ := he
  refine ⟨(F n)ᶜ, (hFc n).isOpen_compl.mem_nhds hn, (finite_Iio n).subset ?_⟩
  intro m hm
  by_contra! hnm
  obtain ⟨y, hyF, hyc⟩ := hm
  exact hyc (hFa (le_of_not_gt hnm) hyF)

theorem closed_sequence_property_of_normal_interval_product
    [NormalSpace (X × unitInterval)] : ClosedSequenceProperty X := by
  intro F hFc hFa hFe
  let A : Set (X × unitInterval) := ⋃ n, F n ×ˢ {intervalThreshold n}
  let B : Set (X × unitInterval) := univ ×ˢ {0}
  have hLF := locallyFinite_of_antitone_closed_empty_intersection F hFc hFa hFe
  have hA : IsClosed A := (hLF.prod_right (fun n => {intervalThreshold n})).isClosed_iUnion
    (fun n => (hFc n).prod isClosed_singleton)
  have hB : IsClosed B := isClosed_univ.prod isClosed_singleton
  have hd : Disjoint A B := by
    apply Set.disjoint_left.mpr
    intro p hpA hpB
    obtain ⟨n, hn⟩ := mem_iUnion.mp hpA
    exact intervalThreshold_ne_zero n (hn.2.symm.trans hpB.2)
  obtain ⟨U, V, hUo, hVo, hAU, hBV, hUV⟩ := normal_separation hA hB hd
  refine ⟨fun n => {x | (x, intervalThreshold n) ∈ U},
    (fun n => hUo.preimage (continuous_id.prodMk continuous_const)), ?_, ?_⟩
  · intro n x hx
    exact hAU (mem_iUnion.mpr ⟨n, hx, rfl⟩)
  · apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxV : (x, (0 : unitInterval)) ∈ V := hBV ⟨mem_univ x, rfl⟩
    have ht : Tendsto (fun n => (x, intervalThreshold n)) atTop (𝓝 (x, (0 : unitInterval))) :=
      tendsto_const_nhds.prodMk_nhds intervalThreshold_tendsto
    obtain ⟨n, hn⟩ := (ht.eventually (hVo.mem_nhds hxV)).exists
    exact Set.disjoint_left.mp hUV (mem_iInter.mp hx n) hn

theorem countably_paracompact_of_normal_interval_product
    [NormalSpace (X × unitInterval)] : CountablyParacompact X := by
  let : NormalSpace X := normal_space_of_normal_product (Y := unitInterval)
  exact countablyParacompact_of_closed_sequence_property
    closed_sequence_property_of_normal_interval_product

end Dowker
