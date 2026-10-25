module
public import Solution
-- BEGIN material-imported-definition audit
namespace ComputationalHodge.CircleHodge.Semantics
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.LoopCharacters
open MeasureTheory Set
open scoped InnerProductSpace

example : Circle=(ℝ ⧸ AddSubgroup.zmultiples (1 : ℝ)) := rfl
example : Coefficient=C(AddCircle (1 : ℝ),ℝ) := rfl
example (α : Coefficient) (x : ℝ) : cover α x=α (x : Circle) := rfl
example (α : Coefficient) : mean α=∫ x in (0 : ℝ)..1,α (x : Circle) := rfl
example (α : Coefficient) : ExactCoefficient α ↔
    ∃ F : C(AddCircle (1 : ℝ),ℝ), ContDiff ℝ 1 (fun x : ℝ => F (x : Circle)) ∧
      ∀ x,deriv (fun t : ℝ => F (t : Circle)) x=α (x : Circle) := Iff.rfl
example (α : Coefficient) : HarmonicCoefficient α ↔
    Differentiable ℝ (fun x : ℝ => α (x : Circle)) ∧
      ∀ x,deriv (fun t : ℝ => α (t : Circle)) x=0 := Iff.rfl
example (f : ℝ → ℝ) : ContDiff ℝ 1 f ↔ Differentiable ℝ f ∧ Continuous (deriv f) :=
  contDiff_one_iff_deriv
example (α : Coefficient) (x : ℝ) :
    cover (potential α) x=(∫ t in (0 : ℝ)..x,α (t : Circle))-x*mean α := rfl
example (L : C1Lift) : ContDiff ℝ 1 L.curve ∧ L.curve 0=0 ∧
    ((L.curve 1 : ℝ) : Circle)=0 := ⟨L.smooth,L.source,L.target⟩
example (L : C1Lift) (t : unitInterval) : projectedLoop L t=((L.curve (t : ℝ) : ℝ) : Circle) := rfl
example (α : Coefficient) (L : C1Lift) :
    lineIntegral α L=∫ t in (0 : ℝ)..1,α ((L.curve t : ℝ) : Circle)*deriv L.curve t := rfl
example (α : Coefficient) : energy α=∫ t in (0 : ℝ)..1,(α (t : Circle))^2 := rfl
example (α : Coefficient) : IntervalIntegrable (cover α) volume 0 1 :=
  (cover_continuous α).intervalIntegrable 0 1
example (α : Coefficient) (L : C1Lift) :
    IntervalIntegrable (fun t => cover α (L.curve t)*deriv L.curve t) volume 0 1 :=
  (((cover_continuous α).comp L.smooth.continuous).mul
    (L.smooth.continuous_deriv (by norm_num))).intervalIntegrable 0 1
example (f : ℝ → ℝ) (a b : ℝ) : IntervalIntegrable f volume a b ↔
    IntegrableOn f (Ioc a b) volume ∧ IntegrableOn f (Ioc b a) volume := Iff.rfl
example (f : ℝ → ℝ) (a b : ℝ) : (∫ x in a..b,f x)=
    (∫ x in Ioc a b,f x)-(∫ x in Ioc b a,f x) := rfl
example (ω : Cochain Unit) : ω ∈ Harmonic (geometricPresentation circleSystem) ↔
    (∀ c : Cell (geometricPresentation circleSystem),period c.left ω-period c.right ω=0) ∧
      ∀ z ∈ Exact circleSystem,inner ℝ z ω=0 := by
  constructor
  · intro h; exact ⟨fun c => congrFun h.1 c,h.2⟩
  · rintro ⟨h,horth⟩; exact ⟨funext h,horth⟩
example (α : Coefficient) : (harmonicCochain α : Cochain Unit)=
    characterCochain circleRooting (mean α • circleCharacter) := rfl
example (p : GeometricTrace circleSystem.toGeometricStepSystem 0 0) :
    ∃ L : C1Lift,_root_.Path.Homotopic.Quotient.mk (projectedLoop L)=traceClass p := by
  exact smooth_representative (traceClass p)
example (α : Coefficient) : harmonicCochain α=0 ↔ ExactCoefficient α := zero_harmonic_iff_exact α

end ComputationalHodge.CircleHodge.Semantics
-- END material-imported-definition audit
