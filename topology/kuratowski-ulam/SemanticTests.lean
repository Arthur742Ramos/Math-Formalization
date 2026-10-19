module
public import KUSolution
public import Mathlib.Topology.Order

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

-- Empty spaces are covered by an empty pi-base; no indexed nonempty-member requirement.
example {Y : Type*} [TopologicalSpace Y] [IsEmpty Y] : HasCountablePiBase Y := by
  refine ⟨∅, Set.countable_empty, ?_, ?_⟩
  · simp
  · intro W _ hW
    obtain ⟨y, _⟩ := hW
    exact isEmptyElim y

-- The first factor may have arbitrary large universe and no Baire instance.
example {X : Type u} [TopologicalSpace X] {A : Set (ULift.{v} X × ℕ)}
    (hA : IsMeagre A) : ∀ᶠ x in residual (ULift.{v} X), IsMeagre (Prod.mk x ⁻¹' A) :=
  eventually_isMeagre_sections hasCountablePiBase_of_secondCountable hA

-- An empty family is not a pi-base on a nonempty space.
example {Y : Type*} [TopologicalSpace Y] [Nonempty Y] :
    ¬ IsCountablePiBase (∅ : Set (Set Y)) := by
  intro h
  obtain ⟨V, hV, _⟩ := h.2.2 univ isOpen_univ Set.univ_nonempty
  exact hV

-- The second-countable corollary still allows arbitrary Baire first factors.
example {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [BaireSpace X] [BaireSpace Y] [SecondCountableTopology Y] : BaireSpace (X × Y) :=
  baireSpace_prod hasCountablePiBase_of_secondCountable

-- Finite discrete spaces: a nonempty open set is not meagre.
example : let : TopologicalSpace Bool := ⊥
    ¬ IsMeagre ({true} : Set Bool) := by
  let : TopologicalSpace Bool := ⊥
  let : DiscreteTopology Bool := discreteTopology_bot Bool
  let : BaireSpace Bool := baire_of_finite
  exact not_isMeagre_of_isOpen (isOpen_discrete _) (singleton_nonempty _)

-- The product theorem is meaningful without Hausdorffness (indiscrete finite factors).
example : let : TopologicalSpace Bool := ⊤
    BaireSpace (Bool × Bool) := by
  let : TopologicalSpace Bool := ⊤
  let : BaireSpace Bool := baire_of_finite
  exact baireSpace_prod hasCountablePiBase_of_secondCountable

-- A pi-base need not cover every point: the one open singleton in Sierpinski space.
example : IsCountablePiBase ({{True}} : Set (Set Prop)) := by
  refine ⟨(finite_singleton _).countable, ?_, ?_⟩
  · intro V hV
    obtain rfl := mem_singleton_iff.mp hV
    exact ⟨isOpen_singleton_true, singleton_nonempty _⟩
  · intro W hW hWne
    have ht : True ∈ W := by
      obtain ⟨p, hpW⟩ := hWne
      by_cases hp : p
      · have he : p = True := propext (iff_true_intro hp)
        simpa only [he] using hpW
      · have he : p = False := propext (iff_false_intro hp)
        subst p
        have htop : W = univ := by simpa only [nhds_false, Filter.mem_top] using hW.mem_nhds hpW
        simp [htop]
    exact ⟨{True}, mem_singleton _, fun p hp => (mem_singleton_iff.mp hp) ▸ ht⟩

example : False ∉ ⋃₀ ({{True}} : Set (Set Prop)) := by simp
