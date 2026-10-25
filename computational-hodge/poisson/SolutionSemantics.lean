module
public import Solution
-- BEGIN material-imported-definition audit
namespace ComputationalHodge.Poisson.Semantics
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.CircleHodge ComputationalHodge.LoopCharacters
open ComputationalHodge.TraceIntegrals ComputationalHodge.ACLifts ComputationalHodge.MetricHodge
open ComputationalHodge.Poisson MeasureTheory Set
open scoped Topology NNReal ContDiff unitInterval
example : CircleHodge.Circle=(ℝ ⧸ AddSubgroup.zmultiples (1 : ℝ)) := rfl
example : Density={ρ : Coefficient // ∀ q,0<ρ q} := rfl
example : RegularDensity={ρ : Density // ContDiff ℝ 1 (cover ρ.val)} := rfl
example : (C2Space : Set Coefficient)={u | ContDiff ℝ 2 (cover u)} := rfl
example (u : C2Coefficient) : ContDiff ℝ 2 (cover u.val) := u.property
example (f : ℝ→ℝ) : ContDiff ℝ 1 f ↔ Differentiable ℝ f ∧ Continuous (deriv f) := contDiff_one_iff_deriv
example (f : ℝ→ℝ) : ContDiff ℝ 2 f ↔ Differentiable ℝ f ∧ ContDiff ℝ 1 (deriv f) := by
  rw [show (2 : ℕ∞ω)=(1 : ℕ∞ω)+1 from rfl,contDiff_succ_iff_deriv]
  simp
example (ρ : RegularDensity) (u : C2Coefficient) (x : ℝ) :
    cover (laplacian ρ u) x=-(deriv (fun t => deriv (cover u.val) t/cover ρ.val.val t) x)/cover ρ.val.val x := rfl
example (ρ : RegularDensity) (f : Coefficient) : weightedMean ρ f=
    ∫ x in (0 : ℝ)..1,cover ρ.val.val x*cover f x := rfl
example (ρ : RegularDensity) (f : Coefficient) : weightedMean ρ f=
    ∫ q : CircleHodge.Circle,ρ.val.val q*f q := mean_circle (ρ.val.val*f)
example (ρ : RegularDensity) (f : Coefficient) (q : CircleHodge.Circle) :
    projectForcing ρ f q=f q-weightedMean ρ f/mean ρ.val.val := rfl
example (ρ : RegularDensity) (u : C2Coefficient) (q : CircleHodge.Circle) :
    (normalize ρ u).val q=u.val q-weightedMean ρ u.val/mean ρ.val.val := rfl
example (ρ : RegularDensity) (f : Coefficient) :
    laplacian ρ (green ρ f)=projectForcing ρ f := green_solves_projected ρ f
example (ρ : RegularDensity) (f : Coefficient) :
    (∃ u : C2Coefficient,laplacian ρ u=f) ↔ mean (ρ.val.val*f)=0 := solvable_iff ρ f
example {α : Type} (P : α→Prop) : (∃! x,P x) ↔ ∃ x,P x ∧ ∀ y,P y→y=x := Iff.rfl
example {f : ℝ→ℝ} : Function.Periodic f 1 ↔ ∀ x,f (x+1)=f x := Iff.rfl
example {f : ℝ→ℝ} {x v : ℝ} : HasDerivAt f v x ↔ HasDerivAtFilter f v (nhds x ×ˢ pure x) := Iff.rfl
example {f : ℝ→ℝ} {a b : ℝ} : IntervalIntegrable f volume a b ↔
    IntegrableOn f (Ioc a b) volume ∧ IntegrableOn f (Ioc b a) volume := Iff.rfl
example (f : CircleHodge.Circle→ℝ) : HasCompactSupport f ↔ IsCompact (closure (Function.support f)) := Iff.rfl
example : Measure.IsOpenPosMeasure (volume : Measure CircleHodge.Circle) := inferInstance
example (P : ℝ→Prop) : (∀ᵐ t : ℝ,P t) ↔ volume {t | ¬P t}=0 := MeasureTheory.ae_iff
example (α : Coefficient) (L : ACLift) : lineIntegral α L=
    ∫ t in (0 : ℝ)..1,α (projectedLoop L (Set.projIcc 0 1 zero_le_one t))*deriv L.val t := rfl
example (p : Trace 0 0) : projectedLoop (fromTrace p)=GeometricTrace.realize p := projected_fromTrace p
example (coch : Cochain Unit) : coch∈Harmonic (geometricPresentation circleSystem) ↔
    (∀ c : Cell (geometricPresentation circleSystem),period c.left coch-period c.right coch=0) ∧
      ∀ z∈Exact circleSystem,inner ℝ z coch=0 := by
  constructor
  · intro h;exact ⟨fun c => congrFun h.1 c,h.2⟩
  · rintro ⟨h,ho⟩;exact ⟨funext h,ho⟩
end ComputationalHodge.Poisson.Semantics
-- END material-imported-definition audit
