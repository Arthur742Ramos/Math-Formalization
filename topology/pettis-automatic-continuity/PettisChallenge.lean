module
public import Mathlib.Topology.Baire.BaireMeasurable
public import Mathlib.Topology.Algebra.Group.Neighborhood
public import Mathlib.Topology.GDelta.Basic
public import Mathlib.Tactic
public import Mathlib.Topology.Bases


@[expose] public section
open Set Filter TopologicalSpace
open scoped Topology Pointwise
namespace PettisAutomatic

/-- Every open inverse image has the property of Baire. -/
abbrev BPPreimages {G H : Type*} [TopologicalSpace G] [TopologicalSpace H]
    (f : G → H) : Prop := ∀ U : Set H, IsOpen U → BaireMeasurableSet (f ⁻¹' U)

/-- Adapted from the credited earlier campaign's open-residual witness. -/
theorem open_residual_witness {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : BaireMeasurableSet A) (hn : ¬ IsMeagre A) :
    ∃ U : Set X, IsOpen U ∧ U.Nonempty ∧
      ∃ S : Set X, S ∈ residual X ∧ U ∩ S ⊆ A := by
  obtain ⟨U, hU, hAU⟩ := hA.residualEq_isOpen
  have hUne : U.Nonempty := by
    by_contra he
    apply hn
    change ∀ᶠ x in residual X, x ∉ A
    filter_upwards [hAU.mem_iff] with x hx
    exact fun hxa => he ⟨x, hx.mp hxa⟩
  refine ⟨U, hU, hUne, {x | x ∈ A ↔ x ∈ U}, hAU.mem_iff, ?_⟩
  exact fun x hx => hx.2.mpr hx.1

/-- Pettis: a nonmeagre Baire-property set in a Baire topological group has
AA⁻¹ as a neighborhood of the identity. No separation hypothesis is required. -/
theorem mul_inv_mem_nhds_one {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [BaireSpace G] {A : Set G}
    (hA : BaireMeasurableSet A) (hn : ¬ IsMeagre A) : A * A⁻¹ ∈ 𝓝 (1 : G) := by
  obtain ⟨U, hU, ⟨x, hx⟩, S, hS, hSA⟩ := open_residual_witness hA hn
  let N : Set G := (fun g : G => g * x) ⁻¹' U
  have hNo : IsOpen N := hU.preimage (continuous_id.mul continuous_const)
  have hN1 : (1 : G) ∈ N := by simpa [N] using hx
  apply mem_of_superset (hNo.mem_nhds hN1)
  intro g hg
  let L : G ≃ₜ G := Homeomorph.mulLeft g⁻¹
  have hpre : L ⁻¹' S ∈ residual G :=
    (tendsto_residual_of_isOpenMap L.continuous L.isOpenMap) hS
  have hW : (U ∩ L ⁻¹' U).Nonempty := by
    refine ⟨g * x, hg, ?_⟩
    change g⁻¹ * (g * x) ∈ U
    simpa [mul_assoc] using hx
  obtain ⟨z, ⟨hzU, hgzU⟩, hzS, hgzS⟩ :=
    (dense_of_mem_residual (inter_mem hS hpre)).inter_open_nonempty
      (U ∩ L ⁻¹' U) (hU.inter (hU.preimage L.continuous)) hW
  have hzA : z ∈ A := hSA ⟨hzU, hzS⟩
  have hgzA : g⁻¹ * z ∈ A := hSA ⟨hgzU, hgzS⟩
  refine ⟨z, hzA, (g⁻¹ * z)⁻¹, ?_, ?_⟩
  · simpa using hgzA
  · group

end PettisAutomatic


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
