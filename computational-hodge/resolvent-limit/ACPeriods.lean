module
public import ACAnalysis
@[expose] public section
namespace ComputationalHodge.ACLifts
open ComputationalPaths.Path.GeometricTopology ComputationalHodge.LoopCharacters ComputationalHodge.CircleHodge ComputationalHodge.TraceIntegrals MeasureTheory Set
open scoped NNReal Topology unitInterval
/-- Every actual raw finite computational trace is admitted without smoothing it. -/
noncomputable def fromTrace (p : Trace 0 0) : ACLift := ⟨actualLift p,
    (actualLift_eq_rawLift p).symm ▸ (rawLift_lipschitz p).choose_spec.lipschitzOnWith.absolutelyContinuousOnInterval,
    (congrFun (actualLift_eq_rawLift p) 0).trans (rawLift_zero p),
    (congrArg (fun f : ℝ→ℝ => (f 1 : CircleHodge.Circle)) (actualLift_eq_rawLift p)).trans (rawLift_one_coe p)⟩
theorem projected_fromTrace (p : Trace 0 0) :
    projectedLoop (fromTrace p)=GeometricTrace.realize p := DFunLike.ext _ _ (fun t => by
    simpa [projectedLoop,fromTrace,actualLift,circleLift,Set.projIcc_of_mem zero_le_one t.property] using
      congrFun (circleCover.liftPath_lifts (GeometricTrace.realize p).toContinuousMap 0 (by simp)) t)
theorem lineIntegral_fromTrace_harmonic (α : Coefficient) (p : Trace 0 0) :
    lineIntegral α (fromTrace p)=period p (meanHarmonic α) := by
  rw [lineIntegral_eq_mean]
  change mean α*actualLift p 1=period p (meanCochain α)
  rw [actualLift_eq_rawLift,rawLift_one,period_mean_count]
theorem lineIntegral_unit (α : Coefficient) :
    lineIntegral α (fromTrace unitTrace)=mean α := by
  rw [lineIntegral_eq_mean]
  change mean α*actualLift unitTrace 1=mean α
  rw [actualLift_eq_rawLift,rawLift_one]
  simp [unitTrace,count]
end ComputationalHodge.ACLifts
