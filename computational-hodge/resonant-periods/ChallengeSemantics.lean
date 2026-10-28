module
public import Challenge
-- BEGIN material-imported-definition audit
namespace ComputationalHodge.ResonantPeriodsPrototype.Semantics
open ComputationalPaths.Path.GeometricTopology
open ComputationalHodge.CircleHodge ComputationalHodge.MetricHodge ComputationalHodge.Poisson
open ComputationalHodge.Arclength ComputationalHodge.ArclengthSpectrum
open ComputationalHodge.LoopCharacters ComputationalHodge.TraceIntegrals ComputationalHodge.ACLifts
open ComputationalHodge.GreenOperator ComputationalHodge.ResonantPeriodsPrototype
open MeasureTheory Set Filter
open scoped ContDiff Topology unitInterval
example : CircleHodge.Circle=(ℝ ⧸ AddSubgroup.zmultiples (1 : ℝ)) := rfl
example : Density={ρ : Coefficient // ∀ q,0<ρ q} := rfl
example : RegularDensity={ρ : Density // ContDiff ℝ 1 (cover ρ.val)} := rfl
example : (C2Space : Set Coefficient)={u | ContDiff ℝ 2 (cover u)} := rfl

example (u : C2Coefficient) : ContDiff ℝ 2 (cover u.val) := u.property
example {f : ℝ→ℝ} : Function.Periodic f 1 ↔ ∀ x,f (x+1)=f x := Iff.rfl

example {f : ℝ→ℝ} {x v : ℝ} : HasDerivAt f v x ↔ HasDerivAtFilter f v (nhds x ×ˢ pure x) := Iff.rfl
example {f : ℝ→ℝ} {a b : ℝ} : IntervalIntegrable f volume a b ↔
    IntegrableOn f (Ioc a b) volume ∧ IntegrableOn f (Ioc b a) volume := Iff.rfl
example (α : Coefficient) (L : ACLift) : lineIntegral α L=
    ∫ t in (0 : ℝ)..1,α (projectedLoop L (Set.projIcc 0 1 zero_le_one t))*deriv L.val t := rfl
example (coch : Cochain Unit) : coch∈Harmonic (geometricPresentation circleSystem) ↔
    (∀ c : Cell (geometricPresentation circleSystem),period c.left coch-period c.right coch=0) ∧
      ∀ z∈Exact circleSystem,inner ℝ z coch=0 := by
  constructor
  · intro h;exact ⟨fun c => congrFun h.1 c,h.2⟩
  · rintro ⟨h,ho⟩;exact ⟨funext h,ho⟩
example (f : ℝ → ℝ) (a b : ℝ) : AbsolutelyContinuousOnInterval f a b ↔
    Tendsto (fun E : ℕ × (ℕ → ℝ × ℝ) =>
      ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2))
      (AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
        𝓟 (AbsolutelyContinuousOnInterval.disjWithin a b)) (𝓝 0) := Iff.rfl


example (α : Coefficient) : mean α = ∫ x in (0 : ℝ)..1, cover α x := rfl
example (ρ : RegularDensity) (f v : Coefficient) : pairing ρ f v =
    ∫ x in (0 : ℝ)..1, cover ρ.val.val x * cover f x * cover v x := rfl
example (ρ : RegularDensity) (u : C2Coefficient) (x : ℝ) :
    cover (flux ρ u) x = deriv (cover u.val) x / cover ρ.val.val x := rfl
example (f : CircleHodge.Circle → ℝ) : Function.support f = {q | f q ≠ 0} := rfl
example (f : CircleHodge.Circle → ℝ) : HasCompactSupport f ↔
    IsCompact (closure (Function.support f)) := Iff.rfl
example (f : CircleHodge.Circle → ℝ) : HasCompactSupport f := HasCompactSupport.of_compactSpace f
example (f : Coefficient) : IsOpen (Function.support f) := f.continuous.isOpen_support
example (μ : Measure CircleHodge.Circle) : μ.IsOpenPosMeasure ↔
    ∀ U : Set CircleHodge.Circle, IsOpen U → U.Nonempty → μ U ≠ 0 :=
  ⟨fun h => h.open_pos, fun h => ⟨h⟩⟩
example : (volume : Measure CircleHodge.Circle).IsOpenPosMeasure := inferInstance
example (z : ℂ) : Complex.exp z = CauSeq.lim (Complex.exp' z) := Complex.exp_def z
example (z : ℂ) : ‖z‖ = Real.sqrt (Complex.normSq z) := Complex.norm_def z
open Classical in
example (μ : Measure ℝ) (f : ℝ → ℝ) : MeasureTheory.integral μ f =
    if _ : CompleteSpace ℝ then
      if hf : Integrable f μ then L1.integral (hf.toL1 f) else 0
    else 0 := MeasureTheory.integral_def μ f

example (k : ℝ) (A B C S : ℝ → ℝ) (x : ℝ) :
    weightedSolution k A B C S x = (C x * B x - S x * A x) / k := rfl
example (A B C S : ℝ → ℝ) (x : ℝ) :
    weightedFlux A B C S x = -(S x * B x + C x * A x) := rfl
example (α : Coefficient) (x : ℝ) : primitive α x = ∫ t in (0 : ℝ)..x, cover α t := rfl
example (ρ : RegularDensity) (u : C2Coefficient) (x : ℝ) :
    cover (laplacian ρ u) x = -(deriv (fun t => deriv (cover u.val) t / cover ρ.val.val t) x) / cover ρ.val.val x := rfl
example (f : ℝ → ℝ) : ContDiff ℝ 1 f ↔ Differentiable ℝ f ∧ Continuous (deriv f) := contDiff_one_iff_deriv
example (f : ℝ → ℝ) : ContDiff ℝ 2 f ↔ Differentiable ℝ f ∧ ContDiff ℝ 1 (deriv f) := by
  rw [show (2 : ℕ∞ω) = (1 : ℕ∞ω) + 1 from rfl, contDiff_succ_iff_deriv]
  simp
example (A B C S R F : ℝ → ℝ) (k x : ℝ) (hk : k ≠ 0) (hunit : C x ^ 2 + S x ^ 2 = 1)
    (hA : HasDerivAt A (R x * F x * C x) x)
    (hB : HasDerivAt B (R x * F x * S x) x)
    (hC : HasDerivAt C (-k * R x * S x) x)
    (hS : HasDerivAt S (k * R x * C x) x) :
    HasDerivAt (weightedSolution k A B C S) (R x * weightedFlux A B C S x) x ∧
    HasDerivAt (weightedFlux A B C S) (-R x * (k ^ 2 * weightedSolution k A B C S x + F x)) x :=
  weighted_solution_derivatives A B C S R F k x hk hunit hA hB hC hS
example (ρ : RegularDensity) (n : ℕ) (hn : 0 < n) (f : Coefficient)
    (hc : pairing ρ f (curvedCosine ρ n).val = 0)
    (hs : pairing ρ f (curvedSine ρ n).val = 0) :
    ∃ u : C2Coefficient, laplacian ρ u - curvedFrequency ρ n • u.val = f :=
  weighted_direct_solution ρ n hn f hc hs
example (ρ : RegularDensity) (n : ℕ) (f : Coefficient) (p : Trace 0 0) :
    IntervalIntegrable (fun t => (ρ.val.val * f * (curvedCosine ρ n).val)
      (projectedLoop (fromTrace p) (Set.projIcc 0 1 zero_le_one t)) * deriv (fromTrace p).val t) volume 0 1 :=
  line_integrand_integrable _ _
example (ρ : RegularDensity) (n : ℕ) (f : Coefficient) (p : Trace 0 0) :
    IntervalIntegrable (fun t => (ρ.val.val * f * (curvedSine ρ n).val)
      (projectedLoop (fromTrace p) (Set.projIcc 0 1 zero_le_one t)) * deriv (fromTrace p).val t) volume 0 1 :=
  line_integrand_integrable _ _
example (ρ : RegularDensity) (f v : Coefficient) :
    pairing ρ f v = mean (ρ.val.val * f * v) := rfl
example (ρ : RegularDensity) (n : ℕ) :
    curvedFrequency ρ n = (2 * Real.pi * (n : ℝ) / mean ρ.val.val) ^ 2 := by
  simp only [curvedFrequency, frequencyN, angular, div_eq_mul_inv]
  ring
example (ρ : RegularDensity) (n : ℕ) (x : ℝ) :
    cover (curvedCosine ρ n).val x = Real.cos (angular n * coordinate ρ.val x) := by
  change cover (pullback ρ (cosineN n)) x = _
  rw [cover_pullback, cosineN_cover]
  congr 1
  dsimp [angular]
  ring
example (ρ : RegularDensity) (n : ℕ) (x : ℝ) :
    cover (curvedSine ρ n).val x = Real.sin (angular n * coordinate ρ.val x) := by
  change cover (pullback ρ (sineN n)) x = _
  rw [cover_pullback, sineN_cover]
  congr 1
  dsimp [angular]
  ring
example (p : Trace 0 0) : projectedLoop (fromTrace p) = GeometricTrace.realize p := projected_fromTrace p
example (α : Coefficient) (p : Trace 0 0) :
    lineIntegral α (fromTrace p) = period p (meanHarmonic α).val := lineIntegral_fromTrace_harmonic α p
example : unitTrace = GeometricTrace.single () := rfl
example : count unitTrace = 1 := rfl
example (α : Coefficient) : lineIntegral α (fromTrace unitTrace) = mean α := unit_trace_integral α
example (ρ : RegularDensity) (f v : Coefficient) :
    (∀ p : Trace 0 0, lineIntegral (ρ.val.val * f * v) (fromTrace p) = 0) ↔ pairing ρ f v = 0 :=
  trace_periods_iff_pairing ρ f v
example (ρ : RegularDensity) (f v : Coefficient) :
    (∀ p : Trace 0 0, period p (meanHarmonic (ρ.val.val * f * v)).val = 0) ↔ pairing ρ f v = 0 :=
  cochain_periods_iff_pairing ρ f v
example (ρ : RegularDensity) (n : ℕ) (hn : 0 < n) (f : Coefficient) :
    (∃ u : Coefficient, ∃ h : ContDiff ℝ 2 (cover u),
      laplacian ρ ⟨u,h⟩ - curvedFrequency ρ n • u = f) ↔
    (∀ p : Trace 0 0, lineIntegral (ρ.val.val * f * (curvedCosine ρ n).val) (fromTrace p) = 0) ∧
    (∀ p : Trace 0 0, lineIntegral (ρ.val.val * f * (curvedSine ρ n).val) (fromTrace p) = 0) := by
  constructor
  · rintro ⟨u,h,hu⟩
    exact (direct_solvable_iff_raw_mode_periods ρ n hn f).mp ⟨⟨u,h⟩,hu⟩
  · intro h
    obtain ⟨u,hu⟩ := (direct_solvable_iff_raw_mode_periods ρ n hn f).mpr h
    exact ⟨u.val,u.property,hu⟩
example (ρ : RegularDensity) (n : ℕ) (hn : 0 < n) (f : Coefficient) :
    (∃ u : Coefficient, ∃ h : ContDiff ℝ 2 (cover u),
      laplacian ρ ⟨u,h⟩ - curvedFrequency ρ n • u = f) ↔
    (∀ p : Trace 0 0, period p (meanHarmonic (ρ.val.val * f * (curvedCosine ρ n).val)).val = 0) ∧
    (∀ p : Trace 0 0, period p (meanHarmonic (ρ.val.val * f * (curvedSine ρ n).val)).val = 0) := by
  constructor
  · rintro ⟨u,h,hu⟩
    exact (direct_solvable_iff_cochain_mode_periods ρ n hn f).mp ⟨⟨u,h⟩,hu⟩
  · intro h
    obtain ⟨u,hu⟩ := (direct_solvable_iff_cochain_mode_periods ρ n hn f).mpr h
    exact ⟨u.val,u.property,hu⟩
-- Literal contracts used to make the weighted solution periodic.
example (f g : ℝ → ℝ) (T : ℝ) (hf : Function.Periodic f T) (hg : Function.Periodic g T) :
    Function.Periodic (f * g) T := hf.mul hg
example (f g : ℝ → ℝ) (T : ℝ) (hf : Function.Periodic f T) (hg : Function.Periodic g T) :
    Function.Periodic (f - g) T := hf.sub hg
example (f g : ℝ → ℝ) (T : ℝ) (hf : Function.Periodic f T) (hg : Function.Periodic g T) :
    Function.Periodic (f / g) T := hf.div hg
end ComputationalHodge.ResonantPeriodsPrototype.Semantics
-- END material-imported-definition audit
