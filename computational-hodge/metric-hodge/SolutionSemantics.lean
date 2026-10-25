module
public import Solution
-- BEGIN material-imported-definition audit
namespace ComputationalHodge.MetricHodge.Semantics
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.CircleHodge ComputationalHodge.LoopCharacters
open ComputationalHodge.TraceIntegrals ComputationalHodge.ACLifts ComputationalHodge.MetricHodge
open MeasureTheory Set
open scoped Topology NNReal unitInterval
example : CircleHodge.Circle=(ℝ ⧸ AddSubgroup.zmultiples (1 : ℝ)) := rfl
example : Density={ρ : Coefficient // ∀ q,0<ρ q} := rfl
example : ACLift={f : ℝ→ℝ // AbsolutelyContinuousOnInterval f 0 1 ∧
    f 0=0 ∧ ((f 1 : ℝ) : CircleHodge.Circle)=0} := rfl
example (ρ : Density) (α : Coefficient) (q : CircleHodge.Circle) :
    starOne ρ α q=α q/ρ.val q := rfl
example (ρ : Density) (φ : Coefficient) (q : CircleHodge.Circle) :
    starZero ρ φ q=φ q*ρ.val q := rfl
example (ρ : Density) (α : Coefficient) : MetricHarmonic ρ α ↔
    Differentiable ℝ (cover (starOne ρ α)) ∧
      ∀ x,deriv (cover (starOne ρ α)) x=0 := by
  constructor
  · rintro ⟨hd,hz⟩
    exact ⟨hd,fun x => neg_eq_zero.mp ((div_eq_zero_iff.mp (hz x)).resolve_right
      (density_ne ρ (x : CircleHodge.Circle)))⟩
  · rintro ⟨hd,hz⟩
    exact ⟨hd,fun x => by simp [codifferential,hz]⟩
example (ρ : Density) (α : Coefficient) : weightedEnergy ρ α=
    ∫ x in (0 : ℝ)..1,(cover α x)^2/cover ρ.val x := energy_interval ρ α
example (α : Coefficient) : ExactCoefficient α ↔ ∃ F : Coefficient,
    ContDiff ℝ 1 (cover F) ∧ ∀ x,deriv (cover F) x=cover α x := Iff.rfl
example (f : CircleHodge.Circle→ℝ) : HasCompactSupport f :=
  HasCompactSupport.of_compactSpace f
example (f : CircleHodge.Circle→ℝ) : HasCompactSupport f ↔ IsCompact (closure (Function.support f)) := Iff.rfl
example (f : ℝ→ℝ) : ContDiff ℝ 1 f ↔ Differentiable ℝ f ∧ Continuous (deriv f) := contDiff_one_iff_deriv
example : Measure.IsOpenPosMeasure (volume : Measure CircleHodge.Circle) := inferInstance
example (f g : CircleHodge.Circle→ℝ) (hf : Continuous f) (hg : Continuous g) :
    f=ᵐ[volume]g ↔ f=g := hf.ae_eq_iff_eq volume hg
example (P : ℝ→Prop) : (∀ᵐ t : ℝ,P t) ↔ volume {t | ¬P t}=0 := MeasureTheory.ae_iff
example (α : Coefficient) (L : ACLift) : lineIntegral α L=
    ∫ t in (0 : ℝ)..1,α (projectedLoop L (Set.projIcc 0 1 zero_le_one t))*deriv L.val t := rfl
example (p : Trace 0 0) : projectedLoop (fromTrace p)=GeometricTrace.realize p := projected_fromTrace p
example (ω : Cochain Unit) : ω∈Harmonic (geometricPresentation circleSystem) ↔
    (∀ c : Cell (geometricPresentation circleSystem),period c.left ω-period c.right ω=0) ∧
      ∀ z∈Exact circleSystem,inner ℝ z ω=0 := by
  constructor
  · intro h;exact ⟨fun c => congrFun h.1 c,h.2⟩
  · rintro ⟨h,ho⟩;exact ⟨funext h,ho⟩
end ComputationalHodge.MetricHodge.Semantics
-- END material-imported-definition audit
