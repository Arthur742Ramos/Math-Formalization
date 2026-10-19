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
