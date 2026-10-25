module
public import Obstruction
@[expose] public section
namespace ComputationalHodge.GeometricObstruction
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.PresentationHomology ComputationalHodge.GeometricDescent
open scoped InnerProductSpace
universe u v
variable {A : Type u} [TopologicalSpace A] {E : Type v} [Fintype E] [TopologicalSpace E]
  {S : ContinuousGeometricStepSystem A E}

noncomputable def obstructionClass (P : ScopedGeometricRewritePresentation S) :
    Obstruction P →ₗ[ℝ] ChainH1 P where
  toFun b := (ChainBoundaries P).mkQ ⟨b,nullSpan_le_cycles b.property.1⟩
  map_add' b c := by
    change (ChainBoundaries P).mkQ
      (⟨(b : Cochain E) + c,nullSpan_le_cycles (b + c).property.1⟩ : Cycles S.toGeometricStepSystem) = _
    exact map_add (ChainBoundaries P).mkQ
      ⟨b,nullSpan_le_cycles b.property.1⟩ ⟨c,nullSpan_le_cycles c.property.1⟩
  map_smul' r b := by
    exact map_smul (ChainBoundaries P).mkQ r ⟨b,nullSpan_le_cycles b.property.1⟩

theorem obstructionClass_killed (P : ScopedGeometricRewritePresentation S) (b : Obstruction P) :
    homologyMap P (obstructionClass P b) = 0 := by
  change homologyMap P ((ChainBoundaries P).mkQ _) = 0
  rw [homologyMap_mk]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change (b : Cochain E) ∈ Relations (geometricPresentation S)
  rw [geometric_relations_eq_nullSpan]
  exact b.property.1

noncomputable def obstructionToKernel (P : ScopedGeometricRewritePresentation S) :
    Obstruction P →ₗ[ℝ] LinearMap.ker (homologyMap P) where
  toFun b := ⟨obstructionClass P b,obstructionClass_killed P b⟩
  map_add' b c := Subtype.ext (map_add (obstructionClass P) b c)
  map_smul' r b := Subtype.ext (map_smul (obstructionClass P) r b)

theorem obstructionToKernel_injective (P : ScopedGeometricRewritePresentation S) :
    Function.Injective (obstructionToKernel P) := by
  intro b c he
  have hq := congrArg Subtype.val he
  have hc : (⟨(b : Cochain E),nullSpan_le_cycles b.property.1⟩ : Cycles S.toGeometricStepSystem) -
      ⟨(c : Cochain E),nullSpan_le_cycles c.property.1⟩ ∈ ChainBoundaries P :=
    (Submodule.Quotient.eq (ChainBoundaries P)).mp hq
  have hr : (b : Cochain E) - c ∈ Relations P := hc
  have ho : (b : Cochain E) - c ∈ (Relations P)ᗮ :=
    (Relations P)ᗮ.sub_mem b.property.2 c.property.2
  have hz : (b : Cochain E) - c = 0 := by
    have hi : (b : Cochain E) - c ∈ Relations P ⊓ (Relations P)ᗮ := ⟨hr,ho⟩
    simpa only [Submodule.inf_orthogonal_eq_bot,Submodule.mem_bot] using hi
  exact Subtype.ext (sub_eq_zero.mp hz)

theorem obstructionToKernel_surjective (P : ScopedGeometricRewritePresentation S) :
    Function.Surjective (obstructionToKernel P) := by
  rintro ⟨q,hq⟩
  induction q using Submodule.Quotient.induction_on with | _ z =>
  have hn : (z : Cochain E) ∈ NullSpan S := by
    change homologyMap P ((ChainBoundaries P).mkQ z) = 0 at hq
    rw [homologyMap_mk] at hq
    have hz := (Submodule.Quotient.mk_eq_zero _).mp hq
    change (z : Cochain E) ∈ Relations (geometricPresentation S) at hz
    rwa [geometric_relations_eq_nullSpan] at hz
  let b : Obstruction P := ⟨(z : Cochain E) - (Relations P).starProjection z,
    (NullSpan S).sub_mem hn (presentation_relations_le_nullSpan P ((Relations P).starProjection_apply_mem _)),
    (Relations P).sub_starProjection_mem_orthogonal _⟩
  refine ⟨b,Subtype.ext ?_⟩
  apply (Submodule.Quotient.eq _).mpr
  change ((z : Cochain E) - (Relations P).starProjection z) - z ∈ Relations P
  have hm := (Relations P).neg_mem ((Relations P).starProjection_apply_mem (z : Cochain E))
  convert hm using 1
  abel

/-- Norm preservation uses the inherited quotient norm on the actual old homology. -/
theorem obstructionToKernel_norm (P : ScopedGeometricRewritePresentation S) (b : Obstruction P) :
    ‖obstructionToKernel P b‖ = ‖b‖ := by
  let z : Cycles S.toGeometricStepSystem := ⟨b,nullSpan_le_cycles b.property.1⟩
  have ho : z ∈ (ChainBoundaries P)ᗮ := by
    intro w hw
    exact b.property.2 (w : Cochain E) hw
  have he := (ChainBoundaries P).quotientEquivOrthogonal_mk z ho
  have hn := (ChainBoundaries P).quotientEquivOrthogonal.norm_map ((ChainBoundaries P).mkQ z)
  change ‖(ChainBoundaries P).quotientEquivOrthogonal (Submodule.Quotient.mk z)‖ =
    ‖(Submodule.Quotient.mk z : ChainH1 P)‖ at hn
  rw [he] at hn
  exact hn.symm

/-- The actual geometric homology kernel, with its inherited quotient norm. -/
noncomputable def obstructionKernelEquiv (P : ScopedGeometricRewritePresentation S) :
    Obstruction P ≃ₗᵢ[ℝ] LinearMap.ker (homologyMap P) where
  __ := LinearEquiv.ofBijective (obstructionToKernel P)
    ⟨obstructionToKernel_injective P,obstructionToKernel_surjective P⟩
  norm_map' := obstructionToKernel_norm P

theorem obstructionKernelEquiv_class (P : ScopedGeometricRewritePresentation S) (b : Obstruction P) :
    (obstructionKernelEquiv P b).val =
      (ChainBoundaries P).mkQ ⟨(b : Cochain E),nullSpan_le_cycles b.property.1⟩ := by
  change (obstructionToKernel P b).val = _
  rfl

theorem correction_error_kernel (P : ScopedGeometricRewritePresentation S) (h : Harmonic P) :
    ‖(h : Cochain E) - geometricCorrection P h‖ =
      ‖obstructionKernelEquiv P (obstructionProjection P h)‖ := by
  rw [(obstructionKernelEquiv P).norm_map]
  exact correction_error P h

theorem kernel_error_pythagoras (P : ScopedGeometricRewritePresentation S) (h : Harmonic P)
    (k : Harmonic (geometricPresentation S)) :
    ‖(h : Cochain E) - k‖ ^ 2 =
      ‖obstructionKernelEquiv P (obstructionProjection P h)‖ ^ 2 +
      ‖(geometricCorrection P h : Cochain E) - k‖ ^ 2 := by
  rw [(obstructionKernelEquiv P).norm_map]
  exact approximation_pythagoras P h k

theorem kernel_obstruction_zero_iff (P : ScopedGeometricRewritePresentation S) (h : Harmonic P) :
    obstructionKernelEquiv P (obstructionProjection P h) = 0 ↔
      GeometricInvariant (S := S) (h : Cochain E) := by
  rw [← obstruction_zero_iff_descent P h]
  constructor
  · intro hz
    exact (obstructionKernelEquiv P).injective
      (hz.trans (obstructionKernelEquiv P).toLinearEquiv.map_zero.symm)
  · intro hz
    rw [hz]
    exact (obstructionKernelEquiv P).toLinearEquiv.map_zero

end ComputationalHodge.GeometricObstruction
