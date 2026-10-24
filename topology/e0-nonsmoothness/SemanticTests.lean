module
public import E0Solution
public section
open Set Filter TopologicalSpace
open scoped Topology symmDiff
example : EZero.CantorSpace = (ℕ → Bool) := rfl
example (x y : EZero.CantorSpace) : EZero.E0 x y ↔ ∃ N : ℕ, ∀ n, N ≤ n → x n = y n := Iff.rfl
example : (inferInstance : TopologicalSpace Bool) = ⊥ := rfl
example : (inferInstance : TopologicalSpace EZero.CantorSpace) = Pi.topologicalSpace := rfl
example : (inferInstance : TopologicalSpace EZero.CantorSpace) =
    ⨅ n : ℕ, TopologicalSpace.induced (fun x : ℕ → Bool => x n) (⊥ : TopologicalSpace Bool) := rfl
example : BaireSpace EZero.CantorSpace := inferInstance
example (s : Finset ℕ) (x : EZero.CantorSpace) (n : ℕ) :
    EZero.flip s x n = Bool.xor (decide (n ∈ s)) (x n) := rfl
example (m : ℕ → Bool) (x : EZero.CantorSpace) (n : ℕ) :
    EZero.maskHomeomorph m x n = Bool.xor (m n) (x n) := rfl
example (s : Finset ℕ) : (s : Set ℕ).Finite := s.finite_toSet
example {Y : Type*} [TopologicalSpace Y] (f : EZero.CantorSpace → Y) :
    EZero.BPPreimages f ↔ ∀ U : Set Y, IsOpen U → BaireMeasurableSet (f ⁻¹' U) := Iff.rfl
example {Y : Type*} [TopologicalSpace Y] [SecondCountableTopology Y] [T0Space Y]
    (f : EZero.CantorSpace → Y) (hBP : EZero.BPPreimages f)
    (hinv : ∀ x y, EZero.E0 x y → f x = f y) :
    ∃ v : Y, {x : EZero.CantorSpace | f x = v} ∈ residual EZero.CantorSpace :=
  EZero.generically_constant f hBP hinv
example {Y : Type*} [TopologicalSpace Y] [SecondCountableTopology Y] [T0Space Y]
    (f : EZero.CantorSpace → Y)
    (hf : @Measurable EZero.CantorSpace Y (borel EZero.CantorSpace) (borel Y) f) :
    ¬ ∀ x y, EZero.E0 x y ↔ f x = f y := EZero.no_borel_reduction f hf
example {Y : Type*} [TopologicalSpace Y] : T0Space Y ↔
    ∀ x y : Y, x ≠ y → ∃ U : Set Y, IsOpen U ∧ Xor (x ∈ U) (y ∈ U) :=
  t0Space_iff_exists_isOpen_xor_mem Y
example {Y : Type*} [t : TopologicalSpace Y] [SecondCountableTopology Y] :
    ∃ B : Set (Set Y), B.Countable ∧ t = TopologicalSpace.generateFrom B :=
  SecondCountableTopology.is_open_generated_countable
example {Y : Type*} [TopologicalSpace Y] [SecondCountableTopology Y] :
    ∃ B : Set (Set Y), B.Countable ∧ IsTopologicalBasis B := by
  obtain ⟨B, hBc, _, hB⟩ := exists_countable_basis Y
  exact ⟨B, hBc, hB⟩
example {Y : Type*} (B : Set (Set Y)) (U : Set Y) :
    @IsOpen Y (TopologicalSpace.generateFrom B) U ↔ TopologicalSpace.GenerateOpen B U := Iff.rfl
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    Continuous f ↔ ∀ U : Set Y, IsOpen U → IsOpen (f ⁻¹' U) := continuous_def
example {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (f : X → Y) :
    Measurable f ↔ ∀ U : Set Y, MeasurableSet U → MeasurableSet (f ⁻¹' U) := Iff.rfl
example {X : Type*} [TopologicalSpace X] [MeasurableSpace X] :
    BorelSpace X ↔ (inferInstance : MeasurableSpace X) = borel X :=
  ⟨fun h => h.measurable_eq, fun h => ⟨h⟩⟩
-- BEGIN material-imported-definition audit
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
