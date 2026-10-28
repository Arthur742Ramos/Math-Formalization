module
public import Conjugacy
@[expose] public section
namespace ComputationalHodge.ArclengthSpectrum
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.CircleHodge ComputationalHodge.TraceIntegrals
open ComputationalHodge.ACLifts ComputationalHodge.Arclength
open ComputationalHodge.Poisson
open ComputationalHodge.LoopCharacters
open scoped unitInterval

/-- The phase of the actual covering lift of the realized computational trace. -/
noncomputable def tracePhase (ρ : RegularDensity) (n : ℕ) (p : Trace 0 0) (t : ℝ) : ℝ :=
  (n : ℝ) * coordinate ρ.val (actualLift p t)

theorem tracePhase_zero (ρ : RegularDensity) (n : ℕ) (p : Trace 0 0) :
    tracePhase ρ n p 0 = 0 := by
  simp [tracePhase, actualLift_eq_rawLift, rawLift_zero, coordinate_zero]

theorem tracePhase_one (ρ : RegularDensity) (n : ℕ) (p : Trace 0 0) :
    tracePhase ρ n p 1 = (n : ℝ) * (count p : ℝ) := by
  simp [tracePhase, actualLift_eq_rawLift, rawLift_one, coordinate_int]

theorem tracePhase_continuous (ρ : RegularDensity) (n : ℕ) (p : Trace 0 0) :
    Continuous (tracePhase ρ n p) := by
  unfold tracePhase
  rw [actualLift_eq_rawLift]
  exact continuous_const.mul ((coordinate_contDiff_two ρ).continuous.comp (rawLift_continuous p))

/-- The actual mapped loop determined by the phase of the computational trace. -/
noncomputable def phaseLoop (ρ : RegularDensity) (n : ℕ) (p : Trace 0 0) :
    _root_.Path (0 : CircleHodge.Circle) 0 where
  toFun t := ((tracePhase ρ n p (t : ℝ) : ℝ) : CircleHodge.Circle)
  continuous_toFun := (AddCircle.continuous_mk' (1 : ℝ)).comp
    ((tracePhase_continuous ρ n p).comp continuous_subtype_val)
  source' := by simp [tracePhase_zero]
  target' := by
    change ((tracePhase ρ n p 1 : ℝ) : CircleHodge.Circle) = 0
    rw [tracePhase_one]
    apply (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mpr
    exact ⟨(n : ℤ) * count p, by simp [zsmul_eq_mul]⟩

/-- The covering-map winding is the actual trace count multiplied by n. -/
theorem phaseLoop_winding (ρ : RegularDensity) (n : ℕ) (p : Trace 0 0) :
    winding (phaseLoop ρ n p) = (n : ℝ) * (count p : ℝ) := by
  have h : (⟨fun t : unitInterval => tracePhase ρ n p (t : ℝ),
      (tracePhase_continuous ρ n p).comp continuous_subtype_val⟩ : C(unitInterval, ℝ)) =
      circleLift (phaseLoop ρ n p) := by
    apply (circleCover.eq_liftPath_iff' _).mpr
    constructor
    · funext t
      rfl
    · exact tracePhase_zero ρ n p
  unfold winding
  rw [← h]
  exact tracePhase_one ρ n p
end ComputationalHodge.ArclengthSpectrum
