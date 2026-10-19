module
public import KUChallenge

open KuratowskiUlam Set Filter Topology TopologicalSpace

#check KuratowskiUlam.IsCountablePiBase
#check KuratowskiUlam.HasCountablePiBase
#check KuratowskiUlam.hasCountablePiBase_of_secondCountable
#check KuratowskiUlam.eventually_isNowhereDense_sections
#check KuratowskiUlam.eventually_residual_sections
#check KuratowskiUlam.eventually_isMeagre_sections
#check KuratowskiUlam.isMeagre_iff_eventually_sections
#check KuratowskiUlam.residual_iff_eventually_sections
#check KuratowskiUlam.baireSpace_prod

-- Literal definitions, separately checked through each module entrypoint.
example {Y : Type u} [TopologicalSpace Y] (B : Set (Set Y)) :
    IsCountablePiBase B ↔ B.Countable ∧ (∀ V ∈ B, IsOpen V ∧ V.Nonempty) ∧
      ∀ W : Set Y, IsOpen W → W.Nonempty → ∃ V ∈ B, V ⊆ W := Iff.rfl

example {Y : Type u} [TopologicalSpace Y] :
    HasCountablePiBase Y ↔ ∃ B : Set (Set Y), IsCountablePiBase B := Iff.rfl

example {Y : Type u} [TopologicalSpace Y] [SecondCountableTopology Y] :
    HasCountablePiBase Y := hasCountablePiBase_of_secondCountable

-- Independent universes; no Baire, separation or nonempty assumption in forward results.
example {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (hY : HasCountablePiBase Y) {A : Set (X × Y)} (hA : IsNowhereDense A) :
    ∀ᶠ x in residual X, IsNowhereDense (Prod.mk x ⁻¹' A) :=
  eventually_isNowhereDense_sections hY hA

example {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (hY : HasCountablePiBase Y) {A : Set (X × Y)} (hA : A ∈ residual (X × Y)) :
    ∀ᶠ x in residual X, Prod.mk x ⁻¹' A ∈ residual Y :=
  eventually_residual_sections hY hA

example {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (hY : HasCountablePiBase Y) {A : Set (X × Y)} (hA : IsMeagre A) :
    ∀ᶠ x in residual X, IsMeagre (Prod.mk x ⁻¹' A) :=
  eventually_isMeagre_sections hY hA

example {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [BaireSpace X] [BaireSpace Y] (hY : HasCountablePiBase Y)
    {A : Set (X × Y)} (hA : BaireMeasurableSet A) :
    IsMeagre A ↔ ∀ᶠ x in residual X, IsMeagre (Prod.mk x ⁻¹' A) :=
  isMeagre_iff_eventually_sections hY hA

example {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [BaireSpace X] [BaireSpace Y] (hY : HasCountablePiBase Y)
    {A : Set (X × Y)} (hA : BaireMeasurableSet A) :
    A ∈ residual (X × Y) ↔ ∀ᶠ x in residual X, Prod.mk x ⁻¹' A ∈ residual Y :=
  residual_iff_eventually_sections hY hA

example {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [BaireSpace X] [BaireSpace Y] (hY : HasCountablePiBase Y) : BaireSpace (X × Y) :=
  baireSpace_prod hY

-- BEGIN material-imported-definition audit
open scoped symmDiff
-- The literal upstream definition, using the canonical Borel sigma-algebra.
example {Z : Type u} [TopologicalSpace Z] (A : Set Z) :
    BaireMeasurableSet A ↔
      @MeasurableSet Z (eventuallyMeasurableSpace (borel Z) (residual Z)) A := Iff.rfl

example {Z : Type u} [TopologicalSpace Z] (A : Set Z) :
    BaireMeasurableSet A ↔
      ∃ B : Set Z, @MeasurableSet Z (borel Z) B ∧ A =ᶠ[residual Z] B := Iff.rfl

-- Open approximation is a proved upstream equivalence, not definitional equality.
private theorem propertyOfBaire_iff_open_symmDiff_isMeagre
    {Z : Type u} [TopologicalSpace Z] (A : Set Z) :
    BaireMeasurableSet A ↔ ∃ O : Set Z, IsOpen O ∧ IsMeagre (A ∆ O) := by
  rw [BaireMeasurableSet.iff_residualEq_isOpen]
  constructor
  · rintro ⟨O, hO, hAO⟩
    refine ⟨O, hO, ?_⟩
    change ∀ᶠ z in residual Z, z ∉ A ∆ O
    filter_upwards [hAO.mem_iff] with z hz
    simp only [mem_symmDiff]
    tauto
  · rintro ⟨O, hO, hAO⟩
    refine ⟨O, hO, Filter.eventuallyEqSet_iff.mpr ?_⟩
    change ∀ᶠ z in residual Z, z ∉ A ∆ O at hAO
    filter_upwards [hAO] with z hz
    simp only [mem_symmDiff] at hz
    tauto

-- Both original converse contracts follow from the explicit classical hypothesis.
-- No Baire, separation or nonempty hypothesis was needed by the bridge itself.
example {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [BaireSpace X] [BaireSpace Y] (hY : HasCountablePiBase Y)
    {A : Set (X × Y)} (hA : ∃ O, IsOpen O ∧ IsMeagre (A ∆ O)) :
    IsMeagre A ↔ ∀ᶠ x in residual X, IsMeagre (Prod.mk x ⁻¹' A) :=
  isMeagre_iff_eventually_sections hY
    ((propertyOfBaire_iff_open_symmDiff_isMeagre A).mpr hA)

example {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [BaireSpace X] [BaireSpace Y] (hY : HasCountablePiBase Y)
    {A : Set (X × Y)} (hA : ∃ O, IsOpen O ∧ IsMeagre (A ∆ O)) :
    A ∈ residual (X × Y) ↔ ∀ᶠ x in residual X, Prod.mk x ⁻¹' A ∈ residual Y :=
  residual_iff_eventually_sections hY
    ((propertyOfBaire_iff_open_symmDiff_isMeagre A).mpr hA)

example {Z : Type u} [TopologicalSpace Z] {A : Set Z} (hA : BaireMeasurableSet A) :
    ∃ O : Set Z, IsOpen O ∧ IsMeagre (Aᶜ ∆ O) :=
  (propertyOfBaire_iff_open_symmDiff_isMeagre Aᶜ).mp hA.compl
-- END material-imported-definition audit
