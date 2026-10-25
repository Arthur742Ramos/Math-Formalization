module
public import Solution
-- BEGIN material-imported-definition audit
namespace ComputationalHodge.UnitCircleGeometry.Semantics
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.LoopCharacters ComputationalHodge.CircleHodge
open ComputationalHodge.TraceIntegrals ComputationalHodge.ACLifts ComputationalHodge.Dirichlet
open ComputationalHodge.UnitCircleGeometry MeasureTheory Set Complex
open scoped NNReal Topology unitInterval ComplexConjugate
example : CircleHodge.Circle=(ℝ ⧸ AddSubgroup.zmultiples (1 : ℝ)) := rfl
example : ACLift={f : ℝ → ℝ // AbsolutelyContinuousOnInterval f 0 1 ∧ f 0=0 ∧ ((f 1 : ℝ) : CircleHodge.Circle)=0} := rfl
example (P : ℝ → Prop) : (∀ᵐ t : ℝ,P t) ↔ volume {t | ¬P t}=0 := MeasureTheory.ae_iff
example (z v : ℂ) : angularForm z v=(conj z*v).im/(2*Real.pi) := rfl
example (z : ℂ) : ‖z‖=Real.sqrt (z.re*z.re+z.im*z.im) := by rw [Complex.norm_def,Complex.normSq_apply]
example (z : ℂ) : Complex.exp z = CauSeq.lim (Complex.exp' z) := Complex.exp_def z
example (t : ℝ) : ((_root_.Circle.exp t) : ℂ)=Complex.exp (t*Complex.I) := _root_.Circle.coe_exp t
example : volume {(1 : ℝ)}=0 := measure_singleton 1
example (L : ACLift) (t : unitInterval) : circlePath L t=AddCircle.toCircle (projectedLoop L t) := rfl
example (L : ACLift) : AmbientFiniteEnergy L ↔ IntervalIntegrable (fun t => ‖deriv (curve L) t‖^2) volume 0 1 := Iff.rfl
example (L : ACLift) : ambientEnergy L=∫ t in (0 : ℝ)..1,‖deriv (curve L) t‖^2 := rfl
example (L : ACLift) : angularIntegral L=∫ t in (0 : ℝ)..1,angularForm (curve L t) (deriv (curve L) t) := rfl
example (p : Trace 0 0) : embeddedPath (fromTrace p)=(GeometricTrace.realize p).map embedMap.continuous := embedded_fromTrace p
example (L : ACLift) : angularIntegral L=L.val 1 := angular_integral L
example (L : ACLift) : AmbientFiniteEnergy L ↔ FiniteEnergy L := finite_energy_iff L
example (L : ACLift) : _root_.Path.Homotopic (circlePath L) (circlePath (affine L)) := circle_homotopy L
example (ω : Cochain Unit) : ω∈Harmonic (geometricPresentation circleSystem) ↔
    (∀ c : Cell (geometricPresentation circleSystem),period c.left ω-period c.right ω=0) ∧
      ∀ z∈Exact circleSystem,inner ℝ z ω=0 := by
  constructor
  · intro h;exact ⟨fun c => congrFun h.1 c,h.2⟩
  · rintro ⟨h,ho⟩;exact ⟨funext h,ho⟩
end ComputationalHodge.UnitCircleGeometry.Semantics
-- END material-imported-definition audit
