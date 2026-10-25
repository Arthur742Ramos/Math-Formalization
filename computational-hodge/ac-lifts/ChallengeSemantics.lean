module
public import Challenge
-- BEGIN material-imported-definition audit
namespace ComputationalHodge.ACLifts.Semantics
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.LoopCharacters ComputationalHodge.CircleHodge
open ComputationalHodge.TraceIntegrals ComputationalHodge.ACLifts
open MeasureTheory Set
open scoped NNReal Topology unitInterval
example : Circle=(ℝ ⧸ AddSubgroup.zmultiples (1 : ℝ)) := rfl
example : Coefficient=C(AddCircle (1 : ℝ),ℝ) := rfl
example : ACLift={f : ℝ → ℝ // AbsolutelyContinuousOnInterval f 0 1 ∧ f 0=0 ∧ ((f 1 : ℝ) : Circle)=0} := rfl
example (f : ℝ → ℝ) : AbsolutelyContinuousOnInterval f 0 1 ↔
    ∀ ε>0,∃ δ>0,∀ E,E∈AbsolutelyContinuousOnInterval.disjWithin 0 1 →
      ∑ i∈Finset.range E.1,dist (E.2 i).1 (E.2 i).2<δ →
        ∑ i∈Finset.range E.1,dist (f (E.2 i).1) (f (E.2 i).2)<ε :=
  absolutelyContinuousOnInterval_iff f 0 1
example (P : ℝ → Prop) : (∀ᵐ t : ℝ,P t) ↔ volume {t | ¬P t}=0 := MeasureTheory.ae_iff
example (L : ACLift) (t : unitInterval) : circleLift (projectedLoop L) t=L.val (t : ℝ) :=
  actual_lift_on_interval L t
example (α : Coefficient) (L : ACLift) :
    IntervalIntegrable (fun t => cover α (L.val t)*deriv L.val t) volume 0 1 :=
  ComputationalHodge.ACLifts.cover_integrand_integrable α L
example (α : Coefficient) (L : ACLift) : lineIntegral α L=
    ∫ t in (0 : ℝ)..1,α (projectedLoop L (Set.projIcc 0 1 zero_le_one t))*deriv L.val t := rfl
example (p : Trace 0 0) : projectedLoop (fromTrace p)=GeometricTrace.realize p := projected_fromTrace p
example (α : Coefficient) (p : Trace 0 0) : lineIntegral α (fromTrace p)=rawIntegral α p := lineIntegral_fromTrace α p
example (α : Coefficient) (p : Trace 0 0) :
    lineIntegral α (fromTrace p)=period p (meanHarmonic α) := lineIntegral_fromTrace_harmonic α p
example : ¬∃ K : ℝ≥0,LipschitzOnWith K rootLift.val (Icc (0 : ℝ) 1) := rootLift_not_lipschitz
example (t : ℝ) : rootLift.val t=Real.sqrt t := rootCurve_eq_sqrt t
example (ω : Cochain Unit) : ω∈Harmonic (geometricPresentation circleSystem) ↔
    (∀ c : Cell (geometricPresentation circleSystem),period c.left ω-period c.right ω=0) ∧
      ∀ z∈Exact circleSystem,inner ℝ z ω=0 := by
  constructor
  · intro h;exact ⟨fun c => congrFun h.1 c,h.2⟩
  · rintro ⟨h,ho⟩;exact ⟨funext h,ho⟩
end ComputationalHodge.ACLifts.Semantics
-- END material-imported-definition audit
