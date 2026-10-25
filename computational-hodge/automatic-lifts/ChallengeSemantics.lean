module
public import Challenge
-- BEGIN material-imported-definition audit
namespace ComputationalHodge.AutomaticLifts.Semantics
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
example (L : ACLift) : AmbientFiniteEnergy L ↔ IntervalIntegrable (fun t => ‖deriv (curve L) t‖^2) volume 0 1 := Iff.rfl
example (L : ACLift) : ambientEnergy L=∫ t in (0 : ℝ)..1,‖deriv (curve L) t‖^2 := rfl
example (L : ACLift) : angularIntegral L=∫ t in (0 : ℝ)..1,angularForm (curve L t) (deriv (curve L) t) := rfl
example (p : Trace 0 0) : embeddedPath (fromTrace p)=(GeometricTrace.realize p).map embedMap.continuous := embedded_fromTrace p
example (L : ACLift) : angularIntegral L=L.val 1 := angular_integral L
example (L : ACLift) : AmbientFiniteEnergy L ↔ FiniteEnergy L := finite_energy_iff L
example (ω : Cochain Unit) : ω∈Harmonic (geometricPresentation circleSystem) ↔
    (∀ c : Cell (geometricPresentation circleSystem),period c.left ω-period c.right ω=0) ∧
      ∀ z∈Exact circleSystem,inner ℝ z ω=0 := by
  constructor
  · intro h;exact ⟨fun c => congrFun h.1 c,h.2⟩
  · rintro ⟨h,ho⟩;exact ⟨funext h,ho⟩
example (f : ℝ→ℂ) (hf : AbsolutelyContinuousOnInterval f 0 1)
    (hn : ∀ t∈Icc (0 : ℝ) 1,‖f t‖=1) (h0 : f 0=1) (h1 : f 1=1) : AmbientLoop :=
  ⟨f,hf,hn,h0,h1⟩
example (F : AmbientLoop) : AbsolutelyContinuousOnInterval F.toFun 0 1 := F.ac
example (u : ℝ→ℝ) (s : Set ℝ) : UniformContinuousOn u s ↔
    ∀ ε>0,∃ δ>0,∀ x∈s,∀ y∈s,dist x y<δ → dist (u x) (u y)<ε :=
  Metric.uniformContinuousOn_iff
example (x : CircleHodge.Circle) : circleEquiv x=AddCircle.toCircle x :=
  AddCircle.homeomorphCircle_apply one_ne_zero x
example (F : AmbientLoop) (t : unitInterval) : (unitPath F t : ℂ)=F.toFun t := rfl
example (F : AmbientLoop) : realLift F=(fun t =>
    circleLift (quotientPath F) (Set.projIcc 0 1 zero_le_one t)) := rfl
example (F : AmbientLoop) : AbsolutelyContinuousOnInterval (canonicalLift F).val 0 1 :=
  realLift_ac F
example (F : AmbientLoop) : angularValue F=
    ∫ t in (0 : ℝ)..1,angularForm (F.toFun t) (deriv F.toFun t) := rfl
example (F : AmbientLoop) : InputFiniteEnergy F ↔
    IntervalIntegrable (fun t => ‖deriv F.toFun t‖^2) volume 0 1 := Iff.rfl
example (F : AmbientLoop) : inputEnergy F=∫ t in (0 : ℝ)..1,‖deriv F.toFun t‖^2 := rfl
example (F : AmbientLoop) : normalTrace F=integerTrace (integer_endpoint F).choose := rfl
example (F : AmbientLoop) : _root_.Path.Homotopic (quotientPath F)
    (GeometricTrace.realize (normalTrace F)) := representative_homotopic F
example (F : AmbientLoop) : period (normalTrace F) unitCochain=angularValue F :=
  (angular_representative F).symm

end ComputationalHodge.AutomaticLifts.Semantics
-- END material-imported-definition audit
