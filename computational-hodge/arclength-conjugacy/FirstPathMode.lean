module
public import ArclengthMode
public import TracePhase
@[expose] public section
namespace ComputationalHodge.ArclengthSpectrum
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.CircleHodge ComputationalHodge.Poisson
open ComputationalHodge.TraceIntegrals ComputationalHodge.ACLifts
open scoped unitInterval

/-- The geometric eigenmode on the actual trace is the cosine of its arclength phase. -/
theorem geometricCosine_on_trace (ρ : RegularDensity) (p : Trace 0 0) (t : unitInterval) :
    (geometricCosine ρ).val (GeometricTrace.realize p t) =
      Real.cos (2 * Real.pi * tracePhase ρ 1 p (t : ℝ)) := by
  have hp := congrArg (fun q : _root_.Path (0 : CircleHodge.Circle) 0 => q t) (projected_fromTrace p)
  change ((actualLift p (t : ℝ) : ℝ) : CircleHodge.Circle) = GeometricTrace.realize p t at hp
  rw [← hp]
  change cover (pullback ρ cosine) (actualLift p t) = _
  rw [cover_pullback, cosine_cover]
  simp [tracePhase]
end ComputationalHodge.ArclengthSpectrum
