module
public import Mathlib.Topology.Baire.BaireMeasurable
public import Mathlib.Topology.Algebra.Group.Neighborhood
public import Mathlib.Topology.GDelta.Basic
public import Mathlib.Tactic

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
