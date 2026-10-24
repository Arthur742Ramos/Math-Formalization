module
public import Mathlib.Topology.Baire.BaireMeasurable
public import Mathlib.Topology.Bases
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.GDelta.Basic
public import Mathlib.Tactic

@[expose] public section
open Set Filter TopologicalSpace
open scoped Topology
namespace BaireRegularization

/-- Category measurability: every open inverse image has the property of Baire. -/
abbrev BPPreimages {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Prop := ∀ U : Set Y, IsOpen U → BaireMeasurableSet (f ⁻¹' U)

/-- Countably many open approximations agree simultaneously off a meagre set.
Shrinking their agreement set to a residual Gδ gives subspace continuity. -/
theorem exists_continuous_restriction {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [SecondCountableTopology Y] (f : X → Y) (hBP : BPPreimages f) :
    ∃ C : Set X, IsGδ C ∧ C ∈ residual X ∧ Continuous (fun x : C => f x) := by
  classical
  obtain ⟨B, hBc, _, hB⟩ := exists_countable_basis Y
  have : Countable B := hBc
  choose O hOo hEO using fun U : B =>
    (hBP U.val (hB.isOpen U.property)).residualEq_isOpen
  have hD : {x : X | ∀ U : B, x ∈ f ⁻¹' U.val ↔ x ∈ O U} ∈ residual X := by
    exact eventually_countable_forall.mpr fun U => (hEO U).mem_iff
  obtain ⟨S, hSo, hSd, hSc, hsub⟩ := mem_residual_iff.mp hD
  have hC : ⋂₀ S ∈ residual X := (countable_sInter_mem hSc).mpr
    fun U hU => residual_of_dense_open (hSo U hU) (hSd U hU)
  refine ⟨⋂₀ S, ⟨S, hSo, hSc, rfl⟩, hC, ?_⟩
  apply continuousOn_iff_continuous_domRestrict.mp
  apply hB.continuousOn_iff.mpr
  intro U hUB
  refine ⟨O ⟨U, hUB⟩, hOo _, ?_⟩
  ext x
  constructor
  · rintro ⟨hf, hx⟩
    exact ⟨(hsub hx ⟨U, hUB⟩).mp hf, hx⟩
  · rintro ⟨ho, hx⟩
    exact ⟨(hsub hx ⟨U, hUB⟩).mpr ho, hx⟩

/-- Relative continuity on a comeagre subset gives the Baire property of all
open inverse images, even when that subset is not Gδ. -/
theorem bpPreimages_of_restriction {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (f : X → Y) {C : Set X} (hC : C ∈ residual X)
    (hf : Continuous (fun x : C => f x)) : BPPreimages f := by
  have hOn : ContinuousOn f C := continuousOn_iff_continuous_domRestrict.mpr hf
  intro U hU
  obtain ⟨O, hOo, heq⟩ := continuousOn_iff'.mp hOn U hU
  apply hOo.baireMeasurableSet.congr
  apply Filter.eventuallyEqSet_iff.mpr
  filter_upwards [hC] with x hx
  have he : x ∈ f ⁻¹' U ↔ x ∈ O := by
    have := Set.ext_iff.mp heq x
    simpa only [mem_inter_iff, hx, and_true] using this
  exact he.symm

/-- Baire measurability is exactly continuity after restricting to some
comeagre Gδ. The source need not be Baire; density is a separate conclusion. -/
theorem bpPreimages_iff_continuous_restriction {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [SecondCountableTopology Y] (f : X → Y) :
    BPPreimages f ↔
      ∃ C : Set X, IsGδ C ∧ C ∈ residual X ∧ Continuous (fun x : C => f x) := by
  constructor
  · exact exists_continuous_restriction f
  · rintro ⟨C, _, hC, hf⟩
    exact bpPreimages_of_restriction f hC hf

/-- In a Baire source the constructed comeagre Gδ is dense. This is relative
continuity, not a claim of ambient continuity at every point of the set. -/
theorem exists_dense_continuous_restriction {X Y : Type*} [TopologicalSpace X]
    [BaireSpace X] [TopologicalSpace Y] [SecondCountableTopology Y]
    (f : X → Y) (hBP : BPPreimages f) :
    ∃ C : Set X, IsGδ C ∧ C ∈ residual X ∧ Dense C ∧ Continuous (fun x : C => f x) := by
  obtain ⟨C, hCg, hCr, hf⟩ := exists_continuous_restriction f hBP
  exact ⟨C, hCg, hCr, dense_of_mem_residual hCr, hf⟩

end BaireRegularization
