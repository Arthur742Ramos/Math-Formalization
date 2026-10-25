module
public import Solution
-- BEGIN material-imported-definition audit
namespace ComputationalHodge.Dirichlet.Semantics
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.LoopCharacters ComputationalHodge.CircleHodge
open ComputationalHodge.TraceIntegrals ComputationalHodge.ACLifts ComputationalHodge.Dirichlet
open MeasureTheory Set
open scoped NNReal Topology unitInterval
example : Circle=(ℝ ⧸ AddSubgroup.zmultiples (1 : ℝ)) := rfl
example : ACLift={f : ℝ → ℝ // AbsolutelyContinuousOnInterval f 0 1 ∧ f 0=0 ∧ ((f 1 : ℝ) : Circle)=0} := rfl
example (f : ℝ → ℝ) : AbsolutelyContinuousOnInterval f 0 1 ↔
    ∀ ε>0,∃ δ>0,∀ E,E∈AbsolutelyContinuousOnInterval.disjWithin 0 1 →
      ∑ i∈Finset.range E.1,dist (E.2 i).1 (E.2 i).2<δ →
        ∑ i∈Finset.range E.1,dist (f (E.2 i).1) (f (E.2 i).2)<ε :=
  absolutelyContinuousOnInterval_iff f 0 1
example (P : ℝ → Prop) : (∀ᵐ t : ℝ,P t) ↔ volume {t | ¬P t}=0 := MeasureTheory.ae_iff
example (L : ACLift) : FiniteEnergy L ↔ IntervalIntegrable (fun t => (deriv L.val t)^2) volume 0 1 := Iff.rfl
example (L : ACLift) : energy L=∫ t in (0 : ℝ)..1,(deriv L.val t)^2 := rfl
example (L : ACLift) (t : unitInterval) : circleLift (projectedLoop L) t=L.val (t : ℝ) := actual_lift_on_interval L t
example (p : Trace 0 0) : projectedLoop (fromTrace p)=GeometricTrace.realize p := projected_fromTrace p
example (p : Trace 0 0) : FiniteEnergy (fromTrace p) := fromTrace_finite p
example (L : ACLift) : _root_.Path.Homotopic (projectedLoop L) (projectedLoop (affine L)) := affine_homotopic L
example (L : ACLift) (h : FiniteEnergy L) : energy L=(L.val 1)^2 ↔
    ∀ t∈Icc (0 : ℝ) 1,L.val t=L.val 1*t := minimum_iff_affine L h
example (ω : Cochain Unit) : ω∈Harmonic (geometricPresentation circleSystem) ↔
    (∀ c : Cell (geometricPresentation circleSystem),period c.left ω-period c.right ω=0) ∧
      ∀ z∈Exact circleSystem,inner ℝ z ω=0 := by
  constructor
  · intro h;exact ⟨fun c => congrFun h.1 c,h.2⟩
  · rintro ⟨h,ho⟩;exact ⟨funext h,ho⟩
end ComputationalHodge.Dirichlet.Semantics
-- END material-imported-definition audit
