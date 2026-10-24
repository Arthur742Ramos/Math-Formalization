module
public import RegularSolution
public section
open Set Filter TopologicalSpace
open scoped Topology symmDiff
#check BaireRegularization.bpPreimages_iff_continuous_restriction
#check BaireRegularization.exists_dense_continuous_restriction
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SecondCountableTopology Y] (f : X → Y) :
    (∀ U : Set Y, IsOpen U → BaireMeasurableSet (f ⁻¹' U)) ↔
      ∃ C : Set X, IsGδ C ∧ C ∈ residual X ∧ Continuous (fun x : C => f x) :=
  BaireRegularization.bpPreimages_iff_continuous_restriction f
example {X Y : Type*} [TopologicalSpace X] [BaireSpace X] [TopologicalSpace Y]
    [SecondCountableTopology Y] (f : X → Y)
    (h : ∀ U : Set Y, IsOpen U → BaireMeasurableSet (f ⁻¹' U)) :
    ∃ C : Set X, IsGδ C ∧ C ∈ residual X ∧ Dense C ∧ Continuous (fun x : C => f x) :=
  BaireRegularization.exists_dense_continuous_restriction f h
-- BEGIN material-imported-definition audit
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    BaireRegularization.BPPreimages f ↔ ∀ U : Set Y, IsOpen U → BaireMeasurableSet (f ⁻¹' U) := Iff.rfl
example {X : Type*} [t : TopologicalSpace X] (C : Set X) :
    (inferInstance : TopologicalSpace C) = TopologicalSpace.induced ((↑) : C → X) t := rfl
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) (C : Set X) :
    Continuous (fun x : C => f x) ↔ ContinuousOn f C := continuousOn_iff_continuous_domRestrict.symm
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) (C : Set X) :
    ContinuousOn f C ↔ ∀ U : Set Y, IsOpen U → ∃ O : Set X,
      IsOpen O ∧ f ⁻¹' U ∩ C = O ∩ C := continuousOn_iff'
example {Y : Type*} [t : TopologicalSpace Y] [SecondCountableTopology Y] :
    ∃ B : Set (Set Y), B.Countable ∧ t = TopologicalSpace.generateFrom B :=
  SecondCountableTopology.is_open_generated_countable
example {Y : Type*} (B : Set (Set Y)) (U : Set Y) :
    @IsOpen Y (TopologicalSpace.generateFrom B) U ↔ TopologicalSpace.GenerateOpen B U := Iff.rfl
example {Y : Type*} [TopologicalSpace Y] [SecondCountableTopology Y] :
    ∃ B : Set (Set Y), B.Countable ∧ IsTopologicalBasis B := by
  obtain ⟨B, hBc, _, hB⟩ := exists_countable_basis Y
  exact ⟨B, hBc, hB⟩
example {X : Type*} [TopologicalSpace X] (C : Set X) :
    IsGδ C ↔ ∃ S : Set (Set X), (∀ U ∈ S, IsOpen U) ∧ S.Countable ∧ C = ⋂₀ S := Iff.rfl
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    Continuous f ↔ ∀ U : Set Y, IsOpen U → IsOpen (f ⁻¹' U) := continuous_def
example {X : Type*} [TopologicalSpace X] [BaireSpace X] {C : Set X}
    (hC : C ∈ residual X) : Dense C := dense_of_mem_residual hC
example {X : Type*} [TopologicalSpace X] (A : Set X) : IsMeagre A ↔ Aᶜ ∈ residual X := Iff.rfl
example {X : Type*} [TopologicalSpace X] (A : Set X) : IsNowhereDense A ↔ interior (closure A) = ∅ := Iff.rfl
example {X : Type*} [TopologicalSpace X] (A : Set X) : A ∈ residual X ↔
    ∃ S : Set (Set X), (∀ U ∈ S, IsOpen U) ∧ (∀ U ∈ S, Dense U) ∧
      S.Countable ∧ ⋂₀ S ⊆ A := mem_residual_iff
example {X : Type*} [TopologicalSpace X] (A : Set X) :
    BaireMeasurableSet A ↔ @MeasurableSet X (eventuallyMeasurableSpace (borel X) (residual X)) A := Iff.rfl
example {X : Type*} [TopologicalSpace X] (A : Set X) :
    BaireMeasurableSet A ↔ ∃ O : Set X, IsOpen O ∧ IsMeagre (A ∆ O) := by
  rw [BaireMeasurableSet.iff_residualEq_isOpen]
  constructor
  · rintro ⟨O, hO, hAO⟩
    refine ⟨O, hO, ?_⟩
    change ∀ᶠ x in residual X, x ∉ A ∆ O
    filter_upwards [hAO.mem_iff] with x hx
    simp only [mem_symmDiff]
    tauto
  · rintro ⟨O, hO, hAO⟩
    refine ⟨O, hO, Filter.eventuallyEqSet_iff.mpr ?_⟩
    change ∀ᶠ x in residual X, x ∉ A ∆ O at hAO
    filter_upwards [hAO] with x hx
    simp only [mem_symmDiff] at hx
    tauto
-- END material-imported-definition audit
