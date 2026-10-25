module
public import Solution
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
-- BEGIN material-imported-definition audit
namespace ComputationalHodge.Arclength.Semantics
open ComputationalHodge.CircleHodge ComputationalHodge.LoopCharacters
open ComputationalHodge.TraceIntegrals ComputationalHodge.ACLifts
open ComputationalHodge.MetricHodge ComputationalHodge.Arclength
open MeasureTheory Set
open scoped Topology NNReal unitInterval
example : CircleHodge.Circle=(ℝ ⧸ AddSubgroup.zmultiples (1 : ℝ)) := rfl
example : Density={ρ : Coefficient // ∀ q,0<ρ q} := rfl
example : ACLift={f : ℝ→ℝ // AbsolutelyContinuousOnInterval f 0 1 ∧
    f 0=0 ∧ ((f 1 : ℝ) : CircleHodge.Circle)=0} := rfl
example (ρ : Density) (x : ℝ) : coordinate ρ x=(∫ t in (0 : ℝ)..x,cover ρ.val t)/mean ρ.val := rfl
example (ρ : Density) (x : ℝ) : inverse ρ x=(coordinateHomeomorph ρ).symm x := rfl
example (ρ : Density) (x : ℝ) : coordinate ρ (inverse ρ x)=x := coordinate_inverse ρ x
example (ρ : Density) (L : ACLift) (t : ℝ) : (minimizer ρ L).val t=inverse ρ (L.val 1*t) := rfl
example (ρ : Density) (L : ACLift) : WeightedFiniteEnergy ρ L ↔
    IntervalIntegrable (fun t => (cover ρ.val (L.val t)*deriv L.val t)^2) volume 0 1 := Iff.rfl
example (ρ : Density) (L : ACLift) : Arclength.energy ρ L=
    ∫ t in (0 : ℝ)..1,(cover ρ.val (L.val t)*deriv L.val t)^2 := rfl
example (ρ : Density) (L : ACLift) : WeightedFiniteEnergy ρ L ↔
    Dirichlet.FiniteEnergy (transformed ρ L) := finite_iff ρ L
example (L M : ACLift) : EqOn L.val M.val (Icc 0 1) ↔
    ∀ x,0≤x→x≤1→L.val x=M.val x := by
  constructor
  · intro h x hx hy;exact h ⟨hx,hy⟩
  · intro h x hx;exact h x hx.1 hx.2
example {f : ℝ→ℝ} : Function.Surjective f ↔ ∀ y,∃ x,f x=y := Iff.rfl
example {f : ℝ→ℝ} : StrictMono f ↔ ∀ ⦃a b⦄,a<b→f a<f b := Iff.rfl
example {f : ℝ→ℝ} : Function.Periodic f 1 ↔ ∀ x,f (x+1)=f x := Iff.rfl
example {f : ℝ→ℝ} {a : ℝ} : ContinuousAt f a ↔
    Filter.Tendsto f (nhds a) (nhds (f a)) := Iff.rfl
example {f : ℝ→ℝ} {s : Set ℝ} : ContinuousOn f s ↔
    ∀ x∈s,ContinuousWithinAt f s x := Iff.rfl
example {f : ℝ→ℝ} {x v : ℝ} : HasDerivAt f v x ↔
    HasDerivAtFilter f v (nhds x ×ˢ pure x) := Iff.rfl
example {f : ℝ→ℝ} {a b : ℝ} : IntervalIntegrable f volume a b ↔
    IntegrableOn f (Ioc a b) volume ∧ IntegrableOn f (Ioc b a) volume := Iff.rfl
example (ρ : Density) (p : Trace 0 0) :
    Arclength.energy ρ (minimizer ρ (fromTrace p))=(period p (meanHarmonic ρ.val).val)^2 :=
  computational_minimum ρ p
example (f : CircleHodge.Circle→ℝ) : HasCompactSupport f := HasCompactSupport.of_compactSpace f
example (f : CircleHodge.Circle→ℝ) : HasCompactSupport f ↔ IsCompact (closure (Function.support f)) := Iff.rfl
example (f : ℝ→ℝ) : ContDiff ℝ 1 f ↔ Differentiable ℝ f ∧ Continuous (deriv f) := contDiff_one_iff_deriv
example : Measure.IsOpenPosMeasure (volume : Measure CircleHodge.Circle) := inferInstance
example (P : ℝ→Prop) : (∀ᵐ t : ℝ,P t) ↔ volume {t | ¬P t}=0 := MeasureTheory.ae_iff
example (p : Trace 0 0) : projectedLoop (fromTrace p)=
    ComputationalPaths.Path.GeometricTopology.GeometricTrace.realize p := projected_fromTrace p
example (ω : Cochain Unit) : ω∈Harmonic (geometricPresentation circleSystem) ↔
    (∀ c : Cell (geometricPresentation circleSystem),period c.left ω-period c.right ω=0) ∧
      ∀ z∈Exact circleSystem,inner ℝ z ω=0 := by
  constructor
  · intro h;exact ⟨fun c => congrFun h.1 c,h.2⟩
  · rintro ⟨h,ho⟩;exact ⟨funext h,ho⟩
end ComputationalHodge.Arclength.Semantics
-- END material-imported-definition audit
