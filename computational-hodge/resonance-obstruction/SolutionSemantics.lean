module
public import Solution
-- BEGIN material-imported-definition audit
namespace ComputationalHodge.ResonanceObstruction.Semantics
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.CircleHodge ComputationalHodge.LoopCharacters
open ComputationalHodge.TraceIntegrals ComputationalHodge.ACLifts ComputationalHodge.MetricHodge
open ComputationalHodge.Poisson ComputationalHodge.GreenOperator ComputationalHodge.CircleFredholm
open ComputationalHodge.ResonanceObstruction MeasureTheory Set
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

example (ρ : RegularDensity) (f g : Coefficient) : pairing ρ f g=
    ∫ x in (0 : ℝ)..1,cover ρ.val.val x*cover f x*cover g x := rfl
example (ρ : RegularDensity) (f g : Coefficient) : pairing ρ f g=
    ∫ q : CircleHodge.Circle,ρ.val.val q*f q*g q := mean_circle _
example (ρ : RegularDensity) : Domain ρ={u : C2Coefficient // weightedMean ρ u.val=0} := rfl
example (ρ : RegularDensity) (μ : ℝ) : Resonant ρ μ ↔
    ∃ u : Domain ρ,u.val.val≠0 ∧ laplacian ρ u.val-μ•u.val.val=0 := Iff.rfl
example (ρ : RegularDensity) (μ : ℝ) (u : Domain ρ) (x : ℝ) :
    cover (shifted ρ μ u) x=
      -(deriv (fun t => deriv (cover u.val.val) t/cover ρ.val.val t) x)/cover ρ.val.val x-μ*cover u.val.val x := rfl
example (ρ : RegularDensity) (μ : ℝ) : Resonant ρ μ ↔
    ∃ u : Coefficient,∃ hu : ContDiff ℝ 2 (cover u),
      weightedMean ρ u=0 ∧ u≠0 ∧ laplacian ρ ⟨u,hu⟩-μ•u=0 := by
  constructor
  · rintro ⟨⟨⟨u,hu⟩,hm⟩,hn,he⟩;exact ⟨u,hu,hm,hn,he⟩
  · rintro ⟨u,hu,hm,hn,he⟩;exact ⟨⟨⟨u,hu⟩,hm⟩,hn,he⟩
example (ρ : RegularDensity) (f : Coefficient) : pairing ρ f f=
    ∫ q : CircleHodge.Circle,ρ.val.val q*(f q)^2 := by
  rw [pairing,mean_circle]
  congr 1
  funext q
  change ρ.val.val q*f q*f q=ρ.val.val q*(f q)^2
  ring
example (ρ : RegularDensity) (f g : Coefficient) :
    Integrable (fun q : CircleHodge.Circle => ρ.val.val q*f q*g q) volume :=
  continuous_integrable (ρ.val.val*f*g).continuous
example (ρ : RegularDensity) (u v : C2Coefficient) :
    IntervalIntegrable (fun x => cover (gradient u) x*cover (gradient v) x/cover ρ.val.val x) volume 0 1 :=
  (((cover_continuous (gradient u)).mul (cover_continuous (gradient v))).div
    (cover_continuous ρ.val.val) (fun x => density_ne ρ.val (x : CircleHodge.Circle))).intervalIntegrable 0 1
example (f : CircleHodge.Circle→ℝ) : Function.support f={q | f q≠0} := rfl
example (f : Coefficient) : IsOpen (Function.support f) := f.continuous.isOpen_support
example (μ : Measure CircleHodge.Circle) : μ.IsOpenPosMeasure ↔
    ∀ U : Set CircleHodge.Circle,IsOpen U → U.Nonempty → μ U≠0 :=
  ⟨fun h => h.open_pos,fun h => ⟨h⟩⟩
example : (volume : Measure CircleHodge.Circle).IsOpenPosMeasure := inferInstance
example (U : Set CircleHodge.Circle) (hU : IsOpen U) (h : U.Nonempty) : 0<volume U :=
  hU.measure_pos volume h
example (q : CircleHodge.Circle) : flatDensity.val.val q=1 := rfl
example : frequency=(2*Real.pi)^2 := rfl
example (x : ℝ) : cover cosine x=Real.cos (2*Real.pi*x) := cosine_cover x
example : cosineMode.val.val=cosine ∧ weightedMean flatDensity cosineMode.val.val=0 := ⟨rfl,cosineMode.property⟩
example : (∀ p : Trace 0 0,lineIntegral (flatDensity.val.val*cosine) (fromTrace p)=0) ∧
    ¬∃ u : C2Coefficient,laplacian flatDensity u-frequency•u.val=cosine :=
  ⟨flat_counterexample.2.1,flat_counterexample.2.2.2⟩
end ComputationalHodge.ResonanceObstruction.Semantics
-- END material-imported-definition audit
