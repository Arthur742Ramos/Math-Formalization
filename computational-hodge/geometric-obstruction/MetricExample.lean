module
public import KernelMetric
public import GeometryExample
@[expose] public section
namespace ComputationalHodge.GeometricObstruction
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.PresentationHomology ComputationalHodge.GeometricDescent
open scoped InnerProductSpace

/-- A nonzero old harmonic cochain carried by a geometrically constant generator. -/
noncomputable def constantHarmonic : Harmonic OneLoop.presentation :=
  ⟨OneLoop.coefficient,OneLoop.closedCoefficient.property,by
    rintro _ ⟨f,rfl⟩
    have hz : d0 OneLoop.system.toGeometricStepSystem f = 0 := by
      ext e
      exact sub_self (f ())
    rw [hz,inner_zero_left]⟩

theorem constant_coefficient_null : OneLoop.coefficient ∈ NullSpan OneLoop.system :=
  Submodule.subset_span ⟨constantNullLoop,rfl⟩

theorem constant_obstruction_self :
    (obstructionProjection OneLoop.presentation constantHarmonic : Cochain Unit) =
      OneLoop.coefficient :=
  Submodule.starProjection_eq_self_iff.mpr constant_coefficient_null

theorem constant_correction_zero : geometricCorrection OneLoop.presentation constantHarmonic = 0 := by
  apply Subtype.ext
  change OneLoop.coefficient - (NullSpan OneLoop.system).starProjection OneLoop.coefficient = 0
  rw [Submodule.starProjection_eq_self_iff.mpr constant_coefficient_null,sub_self]

theorem constant_obstruction_nonzero : obstructionProjection OneLoop.presentation constantHarmonic ≠ 0 := by
  intro hz
  have he := congrArg (fun b : Obstruction OneLoop.presentation => (b : Cochain Unit)) hz
  rw [constant_obstruction_self] at he
  have hp := OneLoop.primitive_period
  rw [he,ZeroMemClass.coe_zero,map_zero] at hp
  exact zero_ne_one hp

theorem constant_kernel_error_positive :
    0 < ‖obstructionKernelEquiv OneLoop.presentation
      (obstructionProjection OneLoop.presentation constantHarmonic)‖ := by
  rw [(obstructionKernelEquiv OneLoop.presentation).norm_map]
  exact norm_pos_iff.mpr constant_obstruction_nonzero

end ComputationalHodge.GeometricObstruction
