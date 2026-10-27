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
example (x : ℝ) : cover cosine x=Real.cos (2*Real.pi*x) := cosine_cover x
end ComputationalHodge.ResonanceObstruction.Semantics
-- END material-imported-definition audit
@[expose] public section
namespace ComputationalHodge.ArclengthSpectrum.Semantics
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge
open ComputationalHodge.Poisson ComputationalHodge.Arclength
open ComputationalHodge.ArclengthSpectrum ComputationalHodge.TraceIntegrals
open ComputationalHodge.ACLifts ComputationalHodge.LoopCharacters
open Filter
open scoped Topology unitInterval

-- BEGIN material-imported-definition audit
example (f : ℝ → ℝ) : Function.Surjective f ↔ ∀ y, ∃ x, f x = y := Iff.rfl
example (f : ℝ → ℝ) : StrictMono f ↔ ∀ ⦃a b⦄, a < b → f a < f b := Iff.rfl
example (f : ℝ → ℝ) (a b : ℝ) : AbsolutelyContinuousOnInterval f a b ↔
    Tendsto (fun E : ℕ × (ℕ → ℝ × ℝ) =>
      ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2))
      (AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
        𝓟 (AbsolutelyContinuousOnInterval.disjWithin a b)) (𝓝 0) := Iff.rfl
example (ρ : RegularDensity) : StrictMono (coordinate ρ.val) := coordinate_strictMono ρ.val
example (ρ : RegularDensity) : Function.Surjective (coordinate ρ.val) := coordinate_surjective ρ.val
example (ρ : RegularDensity) : coordinateHomeomorph ρ.val =
    ((coordinate_strictMono ρ.val).orderIsoOfSurjective (coordinate ρ.val)
      (coordinate_surjective ρ.val)).toHomeomorph := rfl
example (ρ : RegularDensity) (x : ℝ) :
    HasDerivAt (coordinate ρ.val) (cover ρ.val.val x / mean ρ.val.val) x :=
  coordinate_hasDerivAt ρ.val x

example (ρ : RegularDensity) (x : ℝ) :
    coordinate ρ.val (inverse ρ.val x) = x := coordinate_inverse ρ.val x

example (ρ : RegularDensity) (u : C2Coefficient) :
    (pullbackC2Equiv ρ).symm (pullbackC2Equiv ρ u) = u := (pullbackC2Equiv ρ).symm_apply_apply u

example (ρ : RegularDensity) (u : C2Coefficient) :
    laplacian ρ (pullbackC2 ρ u) =
      (mean ρ.val.val)⁻¹ ^ 2 • pullback ρ (laplacian ComputationalHodge.ResonanceObstruction.flatDensity u) :=
  laplacian_pullback ρ u

example (ρ : RegularDensity) (n : ℕ) (p : Trace 0 0) :
    winding (phaseLoop ρ n p) = (n : ℝ) * (count p : ℝ) := phaseLoop_winding ρ n p

example (ρ : RegularDensity) (p : Trace 0 0) (t : unitInterval) :
    (geometricCosine ρ).val (GeometricTrace.realize p t) =
      Real.cos (2 * Real.pi * tracePhase ρ 1 p (t : ℝ)) := geometricCosine_on_trace ρ p t

example (ρ : RegularDensity) : (geometricCosine ρ).val ≠ 0 := geometricCosine_nonzero ρ
example : coordinate sampleDensity.val ≠ id := sample_coordinate_nonidentity

example (α : Coefficient) (L : ACLift) :
    IntervalIntegrable (fun t => α (projectedLoop L (Set.projIcc 0 1 zero_le_one t)) * deriv L.val t)
      MeasureTheory.volume 0 1 := line_integrand_integrable α L

example : IsCoveringMap ((↑) : ℝ → AddCircle (1 : ℝ)) := circleCover
example (f : CircleHodge.Circle ≃ₜ CircleHodge.Circle) (q : CircleHodge.Circle) :
    f.symm (f q) = q := f.symm_apply_apply q

example (f : ℝ ≃ₜ ℝ) (f' : ℝ → ℝ) (h₀ : ∀ x, f' x ≠ 0)
    (hf' : ∀ x, HasDerivAt f (f' x) x) (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) :
    ContDiff ℝ 2 (f.symm : ℝ → ℝ) := f.contDiff_symm_deriv h₀ hf' hf
-- END material-imported-definition audit
end ComputationalHodge.ArclengthSpectrum.Semantics
