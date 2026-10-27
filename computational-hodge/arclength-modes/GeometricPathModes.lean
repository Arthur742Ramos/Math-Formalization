module
public import GeometricModes
public import TracePhase
@[expose] public section
namespace ComputationalHodge.ArclengthSpectrum
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.CircleHodge ComputationalHodge.Poisson
open ComputationalHodge.TraceIntegrals ComputationalHodge.ACLifts
open scoped unitInterval

/-- The geometric cosine on the actual realized trace is the cosine of its lifted phase. -/
theorem curvedCosine_on_trace (ρ : RegularDensity) (n : ℕ) (p : Trace 0 0) (t : unitInterval) :
    (curvedCosine ρ n).val (GeometricTrace.realize p t) =
      Real.cos (2 * Real.pi * tracePhase ρ n p (t : ℝ)) := by
  have hp := congrArg (fun q : _root_.Path (0 : CircleHodge.Circle) 0 => q t) (projected_fromTrace p)
  change ((actualLift p (t : ℝ) : ℝ) : CircleHodge.Circle) = GeometricTrace.realize p t at hp
  rw [← hp]
  change cover (pullback ρ (cosineN n)) (actualLift p t) = _
  rw [cover_pullback, cosineN_cover]
  rfl

/-- The same statement for the independent sine mode. -/
theorem curvedSine_on_trace (ρ : RegularDensity) (n : ℕ) (p : Trace 0 0) (t : unitInterval) :
    (curvedSine ρ n).val (GeometricTrace.realize p t) =
      Real.sin (2 * Real.pi * tracePhase ρ n p (t : ℝ)) := by
  have hp := congrArg (fun q : _root_.Path (0 : CircleHodge.Circle) 0 => q t) (projected_fromTrace p)
  change ((actualLift p (t : ℝ) : ℝ) : CircleHodge.Circle) = GeometricTrace.realize p t at hp
  rw [← hp]
  change cover (pullback ρ (sineN n)) (actualLift p t) = _
  rw [cover_pullback, sineN_cover]
  rfl
end ComputationalHodge.ArclengthSpectrum
