module
public import Reconstruction
@[expose] public section

namespace ComputationalHodge.LoopCharacters
open ComputationalPaths.Path.GeometricTopology
universe u v
variable {A : Type u} [TopologicalSpace A] {E : Type v} [Fintype E] [TopologicalSpace E]
  {S : ContinuousGeometricStepSystem A E} {a : A}

theorem characterMap_zero_iff (T : Rooting S a) (ω : Closed (geometricPresentation S)) :
    characterMap a ω = 0 ↔ (ω : Cochain E) ∈ Exact S := by
  rw [← zero_loop_periods_iff_exact T]
  constructor
  · intro h p
    have hg := congrFun (congrArg Subtype.val h) (representedLoop p)
    exact (periodCharacter_loop ω p).symm.trans hg
  · intro h
    apply Subtype.ext
    funext g
    exact h (loopRepresentative g)

noncomputable def harmonicCharacterMap (a : A) :
    Harmonic (geometricPresentation S) →ₗ[ℝ] Characters S a where
  toFun h := periodCharacter ⟨h,h.property.1⟩
  map_add' h k := by
    apply Subtype.ext
    funext g
    exact (period (loopRepresentative g)).map_add _ _
  map_smul' r h := by
    apply Subtype.ext
    funext g
    exact (period (loopRepresentative g)).map_smul r _

theorem harmonicCharacterMap_loop (h : Harmonic (geometricPresentation S))
    (p : GeometricTrace S.toGeometricStepSystem a a) :
    (harmonicCharacterMap a h).val (representedLoop p) = period p h :=
  periodCharacter_loop (⟨(h : Cochain E),h.property.1⟩ : Closed (geometricPresentation S)) p

theorem projection_character (ω : Closed (geometricPresentation S)) :
    harmonicCharacterMap a (harmonicProjection (geometricPresentation S) ω) = characterMap a ω := by
  apply Subtype.ext
  funext g
  exact harmonicProjection_preserves_loop_period (geometricPresentation S) ω (loopRepresentative g)

theorem harmonicCharacterMap_injective (T : Rooting S a) :
    Function.Injective (harmonicCharacterMap (S := S) a) := by
  intro h k heq
  have hp : ∀ p : GeometricTrace S.toGeometricStepSystem a a,
      period p ((h : Cochain E) - k) = 0 := by
    intro p
    have he := congrFun (congrArg Subtype.val heq) (representedLoop p)
    rw [harmonicCharacterMap_loop,harmonicCharacterMap_loop] at he
    rw [map_sub,he,sub_self]
  have hx := (zero_loop_periods_iff_exact T _).mp hp
  have hz := harmonic_exact_zero (geometricPresentation S)
    ((Harmonic (geometricPresentation S)).sub_mem h.property k.property) hx
  exact Subtype.ext (sub_eq_zero.mp hz)

theorem harmonicCharacterMap_surjective (T : Rooting S a) :
    Function.Surjective (harmonicCharacterMap (S := S) a) := by
  intro χ
  obtain ⟨ω,hω⟩ := characterMap_surjective T χ
  exact ⟨harmonicProjection (geometricPresentation S) ω,(projection_character ω).trans hω⟩

/-- Discrete degree-one period correspondence for the actual represented subgroup. -/
noncomputable def harmonicCharacterEquiv (T : Rooting S a) :
    Harmonic (geometricPresentation S) ≃ₗ[ℝ] Characters S a :=
  LinearEquiv.ofBijective (harmonicCharacterMap a)
    ⟨harmonicCharacterMap_injective T,harmonicCharacterMap_surjective T⟩

theorem harmonicCharacterEquiv_loop (T : Rooting S a) (h : Harmonic (geometricPresentation S))
    (p : GeometricTrace S.toGeometricStepSystem a a) :
    (harmonicCharacterEquiv T h).val (representedLoop p) = period p h :=
  harmonicCharacterMap_loop h p

theorem harmonicCharacterEquiv_independent (T U : Rooting S a) :
    harmonicCharacterEquiv T = harmonicCharacterEquiv U := by
  ext h g
  rfl

theorem unique_harmonic_character (T : Rooting S a) (χ : Characters S a) :
    ∃! h : Harmonic (geometricPresentation S),
      ∀ p : GeometricTrace S.toGeometricStepSystem a a,
        period p h = χ.val (representedLoop p) := by
  refine ⟨(harmonicCharacterEquiv T).symm χ,?_,?_⟩
  · intro p
    rw [← harmonicCharacterEquiv_loop T,LinearEquiv.apply_symm_apply]
  · intro h hh
    apply (harmonicCharacterEquiv T).injective
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    funext g
    obtain ⟨p,hp⟩ := g.property
    have hg : g = representedLoop p := Subtype.ext hp.symm
    rw [hg,harmonicCharacterEquiv_loop T,hh p]

end ComputationalHodge.LoopCharacters
