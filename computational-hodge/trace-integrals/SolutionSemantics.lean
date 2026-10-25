module
public import Solution
-- BEGIN material-imported-definition audit
namespace ComputationalHodge.TraceIntegrals.Semantics
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.LoopCharacters ComputationalHodge.CircleHodge
open MeasureTheory Set
open scoped NNReal Topology

example : Circle=(ℝ ⧸ AddSubgroup.zmultiples (1 : ℝ)) := rfl
example : Coefficient=C(AddCircle (1 : ℝ),ℝ) := rfl
example (a b : Circle) : Trace a b=GeometricTrace circleSystem.toGeometricStepSystem a b := rfl
example : unitTrace=(.single () : Trace 0 0) := rfl
example (p : Trace 0 0) (t : ℝ) : actualLift p t=
    circleCover.liftPath (GeometricTrace.realize p).toContinuousMap 0 (by simp)
      (Set.projIcc 0 1 zero_le_one t) := rfl
example (α : Coefficient) (p : Trace 0 0) : rawIntegral α p=
    ∫ t in (0 : ℝ)..1,α (GeometricTrace.realize p (Set.projIcc 0 1 zero_le_one t))*
      deriv (actualLift p) t := rfl
example (p : Trace 0 0) : actualLift p=rawLift p := actualLift_eq_rawLift p
example (α : Coefficient) (p : Trace 0 0) :
    IntervalIntegrable (fun t => α (GeometricTrace.realize p (Set.projIcc 0 1 zero_le_one t))*
      deriv (actualLift p) t) volume 0 1 := raw_integrand_integrable α p
example {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (x : ℝ) : ‖deriv f x‖≤K :=
  norm_deriv_le_of_lipschitz hf
example (f : ℝ → ℝ) : Measurable (deriv f) := measurable_deriv f
example (f : ℝ → ℝ) (a b : ℝ) : IntervalIntegrable f volume a b ↔
    IntegrableOn f (Ioc a b) volume ∧ IntegrableOn f (Ioc b a) volume := Iff.rfl
example (f : ℝ → ℝ) (a b : ℝ) : (∫ x in a..b,f x)=
    (∫ x in Ioc a b,f x)-(∫ x in Ioc b a,f x) := rfl
example (α : Coefficient) : (meanCochain α : Cochain Unit)=WithLp.toLp 2 (fun _ => mean α) := rfl
example (α : Coefficient) : (meanHarmonic α : Cochain Unit)=meanCochain α := rfl
example (ω : Cochain Unit) : ω∈Harmonic (geometricPresentation circleSystem) ↔
    (∀ c : Cell (geometricPresentation circleSystem),period c.left ω-period c.right ω=0) ∧
      ∀ z∈Exact circleSystem,inner ℝ z ω=0 := by
  constructor
  · intro h;exact ⟨fun c => congrFun h.1 c,h.2⟩
  · rintro ⟨h,ho⟩;exact ⟨funext h,ho⟩
example (α : Coefficient) (p : Trace 0 0) : rawIntegral α p=period p (meanHarmonic α) :=
  rawIntegral_harmonic_period α p

end ComputationalHodge.TraceIntegrals.Semantics
-- END material-imported-definition audit
