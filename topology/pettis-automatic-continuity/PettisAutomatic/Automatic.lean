module
public import PettisAutomatic.Category
public import Mathlib.Topology.Bases

@[expose] public section
open Set Filter TopologicalSpace
open scoped Topology Pointwise
namespace PettisAutomatic

/-- A countable dense target set gives a countable right-translate cover.
One preimage is nonmeagre; centers need not lie in the image of f. -/
theorem exists_nonmeagre_right_preimage {G H : Type*} [Group G] [TopologicalSpace G]
    [BaireSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [SeparableSpace H] (f : G → H) {W : Set H} (hW : IsOpen W) (hW1 : (1 : H) ∈ W) :
    ∃ d : H, ¬ IsMeagre (f ⁻¹' ((Homeomorph.mulRight d) '' W)) := by
  obtain ⟨D, hDc, hDd⟩ := exists_countable_dense H
  have hcover : (⋃ d ∈ D, f ⁻¹' ((Homeomorph.mulRight d) '' W)) = univ := by
    apply eq_univ_iff_forall.mpr
    intro g
    let Q : Set H := (fun d : H => f g * d⁻¹) ⁻¹' W
    have hQo : IsOpen Q := hW.preimage (continuous_const.mul continuous_inv)
    have hQne : Q.Nonempty := ⟨f g, by simpa [Q] using hW1⟩
    obtain ⟨d, hdQ, hdD⟩ := hDd.inter_open_nonempty Q hQo hQne
    refine mem_iUnion.mpr ⟨d, mem_iUnion.mpr ⟨hdD, ?_⟩⟩
    refine ⟨f g * d⁻¹, hdQ, ?_⟩
    change (f g * d⁻¹) * d = f g
    group
  have hnot : ¬ IsMeagre (⋃ d ∈ D, f ⁻¹' ((Homeomorph.mulRight d) '' W)) := by
    rw [hcover]
    exact not_isMeagre_of_isOpen isOpen_univ ⟨1, mem_univ 1⟩
  obtain ⟨d, _, hd⟩ := exists_of_not_isMeagre_biUnion hDc hnot
  exact ⟨d, hd⟩

/-- Pettis automatic continuity: a BP-measurable homomorphism from a Baire
topological group to a separable topological group is continuous. The Baire
property concerns inverse images of every open set. No injectivity,
surjectivity, source-Polish or separation premise is assumed. -/
theorem continuous_of_baire_preimages {G H : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [BaireSpace G] [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [SeparableSpace H] (f : G →* H) (hBP : BPPreimages f) :
    Continuous f := by
  apply continuous_of_tendsto_nhds_one f
  intro U hU
  obtain ⟨V, hV, hVV⟩ := exists_nhds_split_inv hU
  obtain ⟨W, hWV, hWo, hW1⟩ := mem_nhds_iff.mp hV
  obtain ⟨d, hd⟩ := exists_nonmeagre_right_preimage (fun x => f x) hWo hW1
  let A : Set G := f ⁻¹' ((Homeomorph.mulRight d) '' W)
  have hA : BaireMeasurableSet A := hBP _ ((Homeomorph.mulRight d).isOpenMap W hWo)
  apply mem_of_superset (mul_inv_mem_nhds_one hA hd)
  rintro z ⟨a, ha, b, hb, rfl⟩
  have hbA : b⁻¹ ∈ A := by simpa using hb
  obtain ⟨w, hw, hwa⟩ := ha
  obtain ⟨v, hv, hvb⟩ := hbA
  change w * d = f a at hwa
  change v * d = f b⁻¹ at hvb
  have hfb : f b = (v * d)⁻¹ := by
    apply inv_injective
    simpa using hvb.symm
  change f (a * b) ∈ U
  rw [map_mul, hwa.symm, hfb]
  simpa [div_eq_mul_inv, mul_inv_rev, mul_assoc] using hVV w (hWV hw) v (hWV hv)

end PettisAutomatic
