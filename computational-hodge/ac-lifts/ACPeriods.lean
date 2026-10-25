module
public import ACAnalysis
@[expose] public section
namespace ComputationalHodge.ACLifts
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.LoopCharacters ComputationalHodge.CircleHodge
open ComputationalHodge.TraceIntegrals
open MeasureTheory Set
open scoped NNReal Topology unitInterval
/-- Every actual raw finite computational trace is admitted without smoothing it. -/
noncomputable def fromTrace (p : Trace 0 0) : ACLift :=
  ⟨actualLift p,by
    obtain ⟨K,hK⟩ := rawLift_lipschitz p
    rw [← actualLift_eq_rawLift] at hK
    exact hK.lipschitzOnWith.absolutelyContinuousOnInterval,
    by rw [actualLift_eq_rawLift,rawLift_zero],
    by rw [actualLift_eq_rawLift,rawLift_one];simp⟩
theorem projected_fromTrace (p : Trace 0 0) :
    projectedLoop (fromTrace p)=GeometricTrace.realize p := by
  ext t
  change ((actualLift p (t : ℝ) : ℝ) : Circle)=GeometricTrace.realize p t
  have h := congrFun (circleCover.liftPath_lifts
    (GeometricTrace.realize p).toContinuousMap 0 (by simp)) t
  simpa [actualLift,circleLift,Set.projIcc_of_mem zero_le_one t.property] using h
theorem lineIntegral_fromTrace (α : Coefficient) (p : Trace 0 0) :
    lineIntegral α (fromTrace p)=rawIntegral α p := by
  unfold lineIntegral
  rw [projected_fromTrace]
  rfl
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
theorem lineIntegral_computational_harmonic (α : Coefficient) (L : ACLift) (p : Trace 0 0)
    (h : _root_.Path.Homotopic (projectedLoop L) (GeometricTrace.realize p)) :
    lineIntegral α L=period p (meanHarmonic α) := by
  rw [← projected_fromTrace p] at h
  rw [lineIntegral_homotopic α L (fromTrace p) h,lineIntegral_fromTrace_harmonic]
theorem unique_harmonic_ac_periods (α : Coefficient) :
    ∃! h : Harmonic (geometricPresentation circleSystem),
      ∀ (L : ACLift) (p : Trace 0 0),
        _root_.Path.Homotopic (projectedLoop L) (GeometricTrace.realize p) →
          lineIntegral α L=period p h := by
  refine ⟨meanHarmonic α,lineIntegral_computational_harmonic α,?_⟩
  intro h hh
  apply Subtype.ext
  ext e
  cases e
  have hp := hh (fromTrace unitTrace) unitTrace
    (by rw [projected_fromTrace])
  rw [lineIntegral_unit] at hp
  exact hp.symm
theorem all_ac_integrals_zero_iff_mean (α : Coefficient) :
    (∀ L : ACLift,lineIntegral α L=0) ↔ mean α=0 := by
  constructor
  · intro h
    have hh := h (fromTrace unitTrace)
    rwa [lineIntegral_unit] at hh
  · intro h L
    rw [lineIntegral_eq_mean,h,zero_mul]
end ComputationalHodge.ACLifts
