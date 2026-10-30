module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Topology.Homotopy.Path
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic.Positivity

@[expose] public section

open MeasureTheory Set
open scoped Interval

namespace MetricGraphResonancePrototype

/-- Derivatives of the two trigonometric modes in a scalar context. -/
theorem trig_mul_derivatives (k x : ℝ) :
    HasDerivAt (fun t : ℝ => Real.sin (k * t)) (k * Real.cos (k * x)) x ∧
      HasDerivAt (fun t : ℝ => Real.cos (k * t)) (-(k * Real.sin (k * x))) x := by
  constructor
  · convert ((hasDerivAt_id x).const_mul k).sin using 1 <;> simp [mul_comm]
  · convert ((hasDerivAt_id x).const_mul k).cos using 1 <;> simp [mul_comm]

theorem sine_wronskian (u q f : ℝ → ℝ) (k x : ℝ)
    (hu : HasDerivAt u (q x) x)
    (hq : HasDerivAt q (-(k ^ 2 * u x + f x)) x) :
    HasDerivAt (fun t => q t * Real.sin (k * t) - k * u t * Real.cos (k * t))
      (-(f x * Real.sin (k * x))) x := by
  have hs := (trig_mul_derivatives k x).1
  have hc := (trig_mul_derivatives k x).2
  convert (hq.mul hs).sub ((hu.const_mul k).mul hc) using 1; ring

theorem sin_squared_positive :
    0 < ∫ x in (0 : ℝ)..1, (Real.sin (2 * Real.pi * x)) ^ 2 := by
  have hk : (2 : ℝ) * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  rw [intervalIntegral.integral_comp_mul_left (fun t : ℝ => (Real.sin t) ^ 2) hk]
  simp only [mul_zero, mul_one, integral_sin_sq, Real.sin_zero, Real.sin_two_pi,
    zero_mul, sub_zero, smul_eq_mul]
  positivity

theorem cosine_wronskian (u q f : ℝ → ℝ) (k x : ℝ)
    (hu : HasDerivAt u (q x) x)
    (hq : HasDerivAt q (-(k ^ 2 * u x + f x)) x) :
    HasDerivAt (fun t => q t * Real.cos (k * t) + k * u t * Real.sin (k * t))
      (-(f x * Real.cos (k * x))) x := by
  have hs := (trig_mul_derivatives k x).1
  have hc := (trig_mul_derivatives k x).2
  convert (hq.mul hc).add ((hu.const_mul k).mul hs) using 1; ring

/-- Sine moment necessity needs only interior derivatives and endpoint
    continuity, so values outside the edge interval are irrelevant. -/
theorem sine_moment_identity_interval (u q f : ℝ → ℝ) (k : ℝ)
    (hucont : ContinuousOn u (Icc 0 1)) (hqcont : ContinuousOn q (Icc 0 1))
    (hu : ∀ x ∈ Ioo 0 1, HasDerivAt u (q x) x)
    (hq : ∀ x ∈ Ioo 0 1, HasDerivAt q (-(k ^ 2 * u x + f x)) x)
    (hf : ContinuousOn f (Icc 0 1)) (hs : Real.sin k = 0) (hc : Real.cos k = 1) :
    (∫ x in (0 : ℝ)..1, f x * Real.sin (k * x)) = k * (u 1 - u 0) := by
  have hwcont : ContinuousOn
      (fun x => q x * Real.sin (k * x) - k * u x * Real.cos (k * x)) (Icc 0 1) := by
    fun_prop
  have hfcont : ContinuousOn (fun x => f x * Real.sin (k * x)) (Icc 0 1) := by
    fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0 : ℝ) ≤ 1)
    hwcont (fun x hx => sine_wronskian u q f k x (hu x hx) (hq x hx))
    (hfcont.neg.intervalIntegrable_of_Icc (by norm_num))
  rw [intervalIntegral.integral_neg] at hi
  simp only [mul_one, mul_zero, Real.sin_zero, Real.cos_zero, hs, hc, zero_sub] at hi
  linarith

/-- Cosine moment necessity under the same interval-only regularity. -/
theorem cosine_moment_identity_interval (u q f : ℝ → ℝ) (k : ℝ)
    (hucont : ContinuousOn u (Icc 0 1)) (hqcont : ContinuousOn q (Icc 0 1))
    (hu : ∀ x ∈ Ioo 0 1, HasDerivAt u (q x) x)
    (hq : ∀ x ∈ Ioo 0 1, HasDerivAt q (-(k ^ 2 * u x + f x)) x)
    (hf : ContinuousOn f (Icc 0 1)) (hs : Real.sin k = 0) (hc : Real.cos k = 1) :
    (∫ x in (0 : ℝ)..1, f x * Real.cos (k * x)) = q 0 - q 1 := by
  have hwcont : ContinuousOn
      (fun x => q x * Real.cos (k * x) + k * u x * Real.sin (k * x)) (Icc 0 1) := by
    fun_prop
  have hfcont : ContinuousOn (fun x => f x * Real.cos (k * x)) (Icc 0 1) := by
    fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0 : ℝ) ≤ 1)
    hwcont (fun x hx => cosine_wronskian u q f k x (hu x hx) (hq x hx))
    (hfcont.neg.intervalIntegrable_of_Icc (by norm_num))
  rw [intervalIntegral.integral_neg] at hi
  simp only [mul_one, mul_zero, Real.sin_zero, Real.cos_zero, hs, hc, add_zero] at hi
  linarith

/-- Scalar identities used in both forced-oscillator derivatives. -/
theorem oscillator_algebra (a r k A B F s c : ℝ) (hk : k ≠ 0) (hsc : s ^ 2 + c ^ 2 = 1) :
    (a * (-(k * s)) + (r / k) * (k * c) +
      ((-(k * s)) * B + c * (F * s) - ((k * c) * A + s * (F * c))) / k =
        -k * a * s + r * c - s * B - c * A) ∧
    ((-k * a) * (k * c) + r * (-(k * s)) - ((k * c) * B + s * (F * s)) -
      ((-(k * s)) * A + c * (F * c)) = -(k ^ 2 * (a * c + (r / k) * s + (c * B - s * A) / k) + F)) := by
  exact ⟨by field_simp [hk]; ring,
    by field_simp [hk]; nlinarith [congrArg (fun z : ℝ => F * z) hsc]⟩

/-- Explicit variation-of-parameters witnesses for a continuous forcing.
    This constructs the solution; it does not assume an ODE solution exists. -/
theorem forced_oscillator_construct (f : ℝ → ℝ) (hf : Continuous f)
    (k a r : ℝ) (hk : k ≠ 0) (hs : Real.sin k = 0) (hc : Real.cos k = 1) :
    ∃ u q : ℝ → ℝ,
      (∀ x, HasDerivAt u (q x) x) ∧
      (∀ x, HasDerivAt q (-(k ^ 2 * u x + f x)) x) ∧
      u 0 = a ∧ q 0 = r ∧
      u 1 = a + (∫ t in (0 : ℝ)..1, f t * Real.sin (k * t)) / k ∧
      q 1 = r - (∫ t in (0 : ℝ)..1, f t * Real.cos (k * t)) := by
  let A : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, f t * Real.cos (k * t)
  let B : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, f t * Real.sin (k * t)
  let u : ℝ → ℝ := fun x => a * Real.cos (k * x) + (r / k) * Real.sin (k * x) +
    (Real.cos (k * x) * B x - Real.sin (k * x) * A x) / k
  let q : ℝ → ℝ := fun x => -k * a * Real.sin (k * x) + r * Real.cos (k * x) -
    Real.sin (k * x) * B x - Real.cos (k * x) * A x
  have hca : Continuous (fun t : ℝ => f t * Real.cos (k * t)) := by fun_prop
  have hcb : Continuous (fun t : ℝ => f t * Real.sin (k * t)) := by fun_prop
  have hA (x : ℝ) : HasDerivAt A (f x * Real.cos (k * x)) x :=
    intervalIntegral.integral_hasDerivAt_right (hca.intervalIntegrable 0 x)
      hca.aestronglyMeasurable.stronglyMeasurableAtFilter hca.continuousAt
  have hB (x : ℝ) : HasDerivAt B (f x * Real.sin (k * x)) x :=
    intervalIntegral.integral_hasDerivAt_right (hcb.intervalIntegrable 0 x)
      hcb.aestronglyMeasurable.stronglyMeasurableAtFilter hcb.continuousAt
  have hsin (x : ℝ) := (trig_mul_derivatives k x).1
  have hcos (x : ℝ) := (trig_mul_derivatives k x).2
  exact ⟨u, q,
    (fun x => ((((hcos x).const_mul a).add ((hsin x).const_mul (r / k))).add
      ((((hcos x).mul (hB x)).sub ((hsin x).mul (hA x))).div_const k)).congr_deriv
      (oscillator_algebra a r k (A x) (B x) (f x)
        (Real.sin (k * x)) (Real.cos (k * x)) hk (Real.sin_sq_add_cos_sq (k * x))).1),
    (fun x => (((((hsin x).const_mul (-k * a)).add ((hcos x).const_mul r)).sub
      ((hsin x).mul (hB x))).sub ((hcos x).mul (hA x))).congr_deriv
      (oscillator_algebra a r k (A x) (B x) (f x)
        (Real.sin (k * x)) (Real.cos (k * x)) hk (Real.sin_sq_add_cos_sq (k * x))).2),
    (by simp [u, A, B]), (by simp [q, A, B]),
    (by simp [u, A, B, hs, hc]), (by simp [q, A, B, hs, hc])⟩

/-- Every continuous edge forcing admits a continuous real-line extension. -/
theorem continuous_edge_extension (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 1)) :
    ∃ g : ℝ → ℝ, Continuous g ∧ EqOn g f (Icc 0 1) := by
  let clamp : ℝ → ℝ := fun x => max 0 (min 1 x)
  have hclamp : Continuous clamp := continuous_const.max (continuous_const.min continuous_id)
  have hmem (x : ℝ) : clamp x ∈ Icc (0 : ℝ) 1 := by
    exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  refine ⟨f ∘ clamp, hf.comp_continuous hclamp hmem, ?_⟩
  intro x hx
  simp [Function.comp_apply, clamp, min_eq_right hx.2, max_eq_right hx.1]

end MetricGraphResonancePrototype

open Finset

namespace MetricGraphResonanceIncidence

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

structure Network (V E : Type*) where
  source : E → V
  target : E → V

def divergence (G : Network V E) (b : E → ℝ) (v : V) : ℝ :=
  (∑ e : E, if G.source e = v then b e else 0) -
    ∑ e : E, if G.target e = v then b e else 0

/-- Finite incidence, presented as a linear map so path flows can be added. -/
def divergenceLinear (G : Network V E) : (E → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun := divergence G
  map_add' := fun b c => funext fun v => by
    simp only [divergence, Pi.add_apply, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun e _ => by split_ifs <;> ring)
  map_smul' := fun a b => funext fun v => by
    simp only [divergence, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun e _ => by split_ifs <;> ring)
def vertexDelta (v : V) : V → ℝ := fun w => if w = v then 1 else 0

omit [Fintype V] in
/-- A unit edge flow creates one source and one sink, including loops. -/
theorem divergence_edge_unit [DecidableEq E] (G : Network V E) (e : E) :
    divergence G (fun j => if j = e then 1 else 0) =
      vertexDelta (G.source e) - vertexDelta (G.target e) := by
  classical
  ext v
  have hsum (endpoint : E → V) :
      (∑ j : E, if endpoint j = v then (if j = e then (1 : ℝ) else 0) else 0) =
        (if endpoint e = v then 1 else 0) := by
    rw [Finset.sum_eq_single e]
    · simp
    · intro j _ hje; simp [hje]
    · intro he; exact (he (Finset.mem_univ e)).elim
  simp only [divergence, vertexDelta, Pi.sub_apply]
  rw [hsum G.source, hsum G.target]
  simp only [eq_comm]

omit [Fintype V] in
/-- Every path in the undirected equivalence closure carries a unit flow
    from its first vertex to its last. -/
theorem reachable_delta_flow (G : Network V E) {a b : V}
    (h : Relation.EqvGen (fun x y => ∃ e, G.source e = x ∧ G.target e = y) a b) :
    ∃ z : E → ℝ, divergence G z = vertexDelta a - vertexDelta b := by
  classical
  induction h with
  | rel x y he =>
      obtain ⟨e, rfl, rfl⟩ := he
      exact ⟨fun j => if j = e then 1 else 0, divergence_edge_unit G e⟩
  | refl x =>
      exact ⟨0, by simpa [divergenceLinear] using (map_zero (divergenceLinear G))⟩
  | symm x y h ih =>
      obtain ⟨z, hz⟩ := ih
      refine ⟨-z, ?_⟩
      change divergenceLinear G (-z) = _
      rw [map_neg]
      change -divergence G z = _
      rw [hz, neg_sub]
  | trans x y z h₁ h₂ ih₁ ih₂ =>
      obtain ⟨z₁, hz₁⟩ := ih₁
      obtain ⟨z₂, hz₂⟩ := ih₂
      refine ⟨z₁ + z₂, ?_⟩
      change divergenceLinear G (z₁ + z₂) = _
      rw [map_add]
      change divergence G z₁ + divergence G z₂ = _
      rw [hz₁, hz₂]
      ring

/-- Connected finite incidence maps onto the zero-total vertex data. -/
theorem exists_divergence_of_sum_zero (G : Network V E) (root : V)
    (connected : ∀ a b, Relation.EqvGen
      (fun x y => ∃ e, G.source e = x ∧ G.target e = y) a b)
    (h : V → ℝ) (hh : ∑ v, h v = 0) :
    ∃ z : E → ℝ, divergence G z = h := by
  classical
  choose z hz using fun v => reachable_delta_flow G (connected v root)
  refine ⟨∑ v, h v • z v, ?_⟩
  change divergenceLinear G (∑ v, h v • z v) = h
  rw [map_sum]
  simp only [map_smul]
  ext w
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ v, h v * divergence G (z v) w) = h w
  simp_rw [hz]
  simp only [Pi.sub_apply]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have hdelta : (∑ v, h v * vertexDelta v w) = h w := by simp [vertexDelta, mul_ite]
  have hroot : (∑ v, h v * vertexDelta root w) = 0 := by rw [← Finset.sum_mul, hh, zero_mul]
  rw [hdelta, hroot, sub_zero]

end MetricGraphResonanceIncidence

namespace MetricGraphResonancePrototype

/-- The interval edge equations, continuity and Kirchhoff conditions. -/
def intervalGraphSolution {V E : Type*} [Fintype E] [DecidableEq V]
    (source target : E → V) (f : E → ℝ → ℝ) (k : ℝ) : Prop :=
  ∃ u q : E → ℝ → ℝ, ∃ vertex : V → ℝ,
    (∀ e, ContinuousOn (u e) (Icc 0 1)) ∧
    (∀ e, ContinuousOn (q e) (Icc 0 1)) ∧
    (∀ e x, x ∈ Set.Ioo 0 1 → HasDerivAt (u e) (q e x) x) ∧
    (∀ e x, x ∈ Set.Ioo 0 1 → HasDerivAt (q e) (-(k ^ 2 * u e x + f e x)) x) ∧
    (∀ e, u e 0 = vertex (source e) ∧ u e 1 = vertex (target e)) ∧
    ∀ v, (∑ e, if source e = v then q e 0 else 0) -
      (∑ e, if target e = v then q e 1 else 0) = 0

/-- The scalar cosine balance and the exact sine moment cochain. -/
def graphMomentConditions {V E : Type*} [Fintype E]
    (source target : E → V) (f : E → ℝ → ℝ) (k : ℝ) : Prop :=
  (∑ e, ∫ t in (0 : ℝ)..1, f e t * Real.cos (k * t)) = 0 ∧
    ∃ p : V → ℝ, ∀ e,
      (∫ t in (0 : ℝ)..1, f e t * Real.sin (k * t)) = p (target e) - p (source e)

theorem interval_graph_moments_necessary
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (source target : E → V) (f : E → ℝ → ℝ)
    (hf : ∀ e, ContinuousOn (f e) (Icc 0 1))
    (k : ℝ) (hs : Real.sin k = 0) (hc : Real.cos k = 1)
    (hsol : intervalGraphSolution source target f k) :
    graphMomentConditions source target f k := by
  classical
  obtain ⟨u, q, vertex, huc, hqc, hu, hq, he, hkir⟩ := hsol
  have hsum : (∑ e, (q e 0 - q e 1)) = 0 := by
    calc
      (∑ e, (q e 0 - q e 1)) = ∑ v, ((∑ e, if source e = v then q e 0 else 0) -
          (∑ e, if target e = v then q e 1 else 0)) := by
        simp [Finset.sum_sub_distrib, Finset.sum_comm]
      _ = 0 := by simp [hkir]
  exact ⟨
    (Finset.sum_congr rfl (fun e _ => cosine_moment_identity_interval
      (u e) (q e) (f e) k (huc e) (hqc e) (hu e) (hq e) (hf e) hs hc)).trans hsum,
    ⟨fun v => k * vertex v, fun e =>
      (sine_moment_identity_interval (u e) (q e) (f e) k (huc e) (hqc e)
        (hu e) (hq e) (hf e) hs hc).trans
        ((congrArg (fun z : ℝ => k * z)
          (congrArg₂ (fun x y : ℝ => x - y) (he e).2 (he e).1)).trans
            (mul_sub k (vertex (target e)) (vertex (source e))))⟩⟩

/-- The edge moment is unchanged when the integrand agrees on the edge. -/
theorem edge_moment_congr (g f w : ℝ → ℝ) (hgf : EqOn g f (Icc 0 1)) :
    (∫ t in (0 : ℝ)..1, g t * w t) = ∫ t in (0 : ℝ)..1, f t * w t := by
  apply intervalIntegral.integral_congr
  intro t ht
  change g t * w t = f t * w t
  rw [hgf (by simpa using ht)]

/-- A flow matching the incoming demand satisfies the Kirchhoff balance. -/
theorem graph_flux_of_divergence {V E : Type*} [Fintype E] [DecidableEq V]
    (source target : E → V) (C flow : E → ℝ)
    (hflow : MetricGraphResonanceIncidence.divergence ⟨source, target⟩ flow =
      fun v => -(∑ e, if target e = v then C e else 0)) (v : V) :
    (∑ e, if source e = v then flow e else 0) -
      (∑ e, if target e = v then flow e - C e else 0) = 0 := by
  have hin : (∑ e, if target e = v then flow e - C e else 0) =
      (∑ e, if target e = v then flow e else 0) -
        (∑ e, if target e = v then C e else 0) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e he
    split_ifs <;> simp
  have hv := congrFun hflow v
  change (∑ e, if source e = v then flow e else 0) -
    (∑ e, if target e = v then flow e else 0) =
      -(∑ e, if target e = v then C e else 0) at hv
  rw [hin]
  linarith

theorem endpoint_from_sine (a b k : ℝ) (hk : k ≠ 0) :
    a + k * (b - a) / k = b := by field_simp [hk]; ring

theorem interval_graph_moments_sufficient
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (source target : E → V) (root : V)
    (connected : ∀ a b, Relation.EqvGen
      (fun x y => ∃ e, source e = x ∧ target e = y) a b)
    (f : E → ℝ → ℝ) (hf : ∀ e, ContinuousOn (f e) (Icc 0 1))
    (k : ℝ) (hk : k ≠ 0) (hs : Real.sin k = 0) (hc : Real.cos k = 1)
    (hmom : graphMomentConditions source target f k) :
    intervalGraphSolution source target f k := by
  classical
  exact
    let ⟨hcos, p, hp⟩ := hmom
    let hExt (e : E) := continuous_edge_extension (f e) (hf e)
    let g : E → ℝ → ℝ := fun e => Classical.choose (hExt e)
    have hg : ∀ e, Continuous (g e) := fun e => (Classical.choose_spec (hExt e)).1
    have hgf : ∀ e, EqOn (g e) (f e) (Icc 0 1) := fun e => (Classical.choose_spec (hExt e)).2
    have hsin (e : E) : (∫ t in (0 : ℝ)..1, g e t * Real.sin (k * t)) =
        ∫ t in (0 : ℝ)..1, f e t * Real.sin (k * t) :=
      edge_moment_congr (g e) (f e) (fun t => Real.sin (k * t)) (hgf e)
    have hcos' (e : E) : (∫ t in (0 : ℝ)..1, g e t * Real.cos (k * t)) =
        ∫ t in (0 : ℝ)..1, f e t * Real.cos (k * t) :=
      edge_moment_congr (g e) (f e) (fun t => Real.cos (k * t)) (hgf e)
    let vertex : V → ℝ := fun v => p v / k
    have hsine (e : E) : (∫ t in (0 : ℝ)..1, g e t * Real.sin (k * t)) =
        k * (vertex (target e) - vertex (source e)) :=
      (hsin e).trans ((hp e).trans
        ((mul_sub k _ _).trans (congrArg₂ (fun a b : ℝ => a - b)
          (mul_div_cancel₀ (p (target e)) hk) (mul_div_cancel₀ (p (source e)) hk))).symm)
    let C : E → ℝ := fun e => ∫ t in (0 : ℝ)..1, g e t * Real.cos (k * t)
    let demand : V → ℝ := fun v => -(∑ e, if target e = v then C e else 0)
    let G : MetricGraphResonanceIncidence.Network V E := ⟨source, target⟩
    have hcosg : (∑ e, C e) = 0 := by simpa only [C, hcos'] using hcos
    have hsum : ∑ v, demand v = 0 := by
      simp [demand, Finset.sum_neg_distrib, Finset.sum_comm, hcosg]
    let ⟨flow, hflow⟩ :=
      MetricGraphResonanceIncidence.exists_divergence_of_sum_zero G root connected demand hsum
    have hflux (v : V) := graph_flux_of_divergence source target C flow hflow v
    let hex (e : E) := forced_oscillator_construct (g e) (hg e) k
      (vertex (source e)) (flow e) hk hs hc
    let u (e : E) := Classical.choose (hex e)
    let q (e : E) := Classical.choose (Classical.choose_spec (hex e))
    have hedge (e : E) := Classical.choose_spec (Classical.choose_spec (hex e))
    have hq0 (e : E) : q e 0 = flow e := (hedge e).2.2.2.1
    have hq1 (e : E) : q e 1 = flow e - C e := (hedge e).2.2.2.2.2
    have hkir (v : V) : (∑ e, if source e = v then q e 0 else 0) -
        (∑ e, if target e = v then q e 1 else 0) = 0 := by
      simpa only [hq0, hq1] using hflux v
    ⟨u, q, vertex,
      fun e => (show Differentiable ℝ (u e) from fun x => ((hedge e).1 x).differentiableAt).continuous.continuousOn,
      fun e => (show Differentiable ℝ (q e) from fun x => ((hedge e).2.1 x).differentiableAt).continuous.continuousOn,
      fun e x _ => (hedge e).1 x, fun e x hx => (hgf e (mem_Icc_of_Ioo hx)) ▸ (hedge e).2.1 x,
      fun e => ⟨(hedge e).2.2.1, ((hedge e).2.2.2.2.1).trans
        (by simpa only [hsine e] using endpoint_from_sine _ _ _ hk)⟩, hkir⟩

theorem forced_connected_graph_interval_iff
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (source target : E → V) (root : V)
    (connected : ∀ a b, Relation.EqvGen
      (fun x y => ∃ e, source e = x ∧ target e = y) a b)
    (f : E → ℝ → ℝ) (hf : ∀ e, ContinuousOn (f e) (Icc 0 1))
    (k : ℝ) (hk : k ≠ 0) (hs : Real.sin k = 0) (hc : Real.cos k = 1) :
    intervalGraphSolution source target f k ↔ graphMomentConditions source target f k :=
  ⟨interval_graph_moments_necessary source target f hf k hs hc,
    interval_graph_moments_sufficient source target root connected f hf k hk hs hc⟩

end MetricGraphResonancePrototype

/-
Copyright (c) 2025 Computational Paths contributors.
Upstream excerpts are MIT licensed; see SOURCE-LICENSE.txt.
Ported at the exact revision recorded in source-provenance.json.
-/
/-! Literal source port of the user's endpoint-changing step system, trace and
realization definitions; the scoped rewrite definitions are omitted. Only imports, module visibility and enclosing namespaces
are adapted. No claim about equality-indexed raw Path or HoTT is made. -/

namespace ComputationalPaths.Path.GeometricTopology
open scoped ContinuousMap Topology
universe u v

structure GeometricStepSystem (A : Type u) [TopologicalSpace A] (Step : Type v) where
  src : Step → A
  tgt : Step → A
  realize : (s : Step) → _root_.Path (src s) (tgt s)

/-- A finite trace of endpoint-changing geometric computations. -/
inductive GeometricTrace {A : Type u} [TopologicalSpace A] {Step : Type v}
    (S : GeometricStepSystem A Step) : A → A → Type (max u v) where
  | refl (a : A) : GeometricTrace S a a
  | single (s : Step) : GeometricTrace S (S.src s) (S.tgt s)
  | trans {a b c : A} :
      GeometricTrace S a b → GeometricTrace S b c → GeometricTrace S a c
  | symm {a b : A} : GeometricTrace S a b → GeometricTrace S b a

namespace GeometricTrace

variable {A : Type u} [TopologicalSpace A] {Step : Type v}
  {S : GeometricStepSystem A Step}

/-- The continuous path obtained by executing a geometric trace. -/
noncomputable def realize {a b : A} : GeometricTrace S a b → _root_.Path a b
  | .refl a => _root_.Path.refl a
  | .single s => S.realize s
  | .trans p q => _root_.Path.trans (realize p) (realize q)
  | .symm p => _root_.Path.symm (realize p)

end GeometricTrace

end ComputationalPaths.Path.GeometricTopology

/-! A first topological realization of an oriented unit-edge graph. The
quotient and edge paths below do not yet prove topological embeddings, an
intrinsic metric, or a line-integral comparison. -/

namespace MetricGraphPathPrototype
open scoped Topology
open scoped Interval
open unitInterval
open MeasureTheory

variable {V E : Type*} [TopologicalSpace V] [TopologicalSpace E]

/-- Identify each edge endpoint with its designated vertex. -/
inductive EdgeGlue (source target : E → V) : V ⊕ (E × I) → V ⊕ (E × I) → Prop
  | source_endpoint (e : E) : EdgeGlue source target (Sum.inr (e, 0)) (Sum.inl (source e))
  | target_endpoint (e : E) : EdgeGlue source target (Sum.inr (e, 1)) (Sum.inl (target e))

def Graph (source target : E → V) := Quot (EdgeGlue source target)

instance (source target : E → V) : TopologicalSpace (Graph source target) :=
  inferInstanceAs (TopologicalSpace (Quot (EdgeGlue source target)))

def vertex (source target : E → V) (v : V) : Graph source target :=
  Quot.mk _ (Sum.inl v)

def edgePoint (source target : E → V) (e : E) (t : I) : Graph source target :=
  Quot.mk _ (Sum.inr (e, t))

omit [TopologicalSpace V] [TopologicalSpace E] in
theorem edgePoint_zero (source target : E → V) (e : E) :
    edgePoint source target e 0 = vertex source target (source e) :=
  Quot.sound (EdgeGlue.source_endpoint e)

omit [TopologicalSpace V] [TopologicalSpace E] in
theorem edgePoint_one (source target : E → V) (e : E) :
    edgePoint source target e 1 = vertex source target (target e) :=
  Quot.sound (EdgeGlue.target_endpoint e)

/-- Each edge chart descends to an actual continuous topological path. -/
noncomputable def edgePath (source target : E → V) (e : E) :
    _root_.Path (vertex source target (source e)) (vertex source target (target e)) where
  toFun := edgePoint source target e
  continuous_toFun := continuous_quot_mk.comp (continuous_inr.comp (continuous_const.prodMk continuous_id))
  source' := edgePoint_zero source target e
  target' := edgePoint_one source target e

/-- Use the user's literal endpoint-changing computational trace interface. -/
noncomputable def edgeStepSystem (source target : E → V) :
    ComputationalPaths.Path.GeometricTopology.GeometricStepSystem (Graph source target) E where
  src e := vertex source target (source e)
  tgt e := vertex source target (target e)
  realize e := edgePath source target e

/-- Edge-chart primitive before passing to the graph quotient. -/
noncomputable def rawPotential (source : E → V) (p : V → ℝ) (w : E → ℝ → ℝ) :
    V ⊕ (E × I) → ℝ
  | Sum.inl v => p v
  | Sum.inr (e, t) => p (source e) + ∫ x in (0 : ℝ)..(t : ℝ), w e x

omit [TopologicalSpace V] [TopologicalSpace E] in
theorem rawPotential_glue (source target : E → V) (p : V → ℝ) (w : E → ℝ → ℝ)
    (hexact : ∀ e, (∫ x in (0 : ℝ)..1, w e x) = p (target e) - p (source e))
    {a b : V ⊕ (E × I)} (h : EdgeGlue source target a b) :
    rawPotential source p w a = rawPotential source p w b := by
  cases h <;> simp [rawPotential, hexact]

/-- A compatible family of edge-chart primitives gives a quotient function. -/
noncomputable def graphPotential (source target : E → V) (p : V → ℝ) (w : E → ℝ → ℝ)
    (hexact : ∀ e, (∫ x in (0 : ℝ)..1, w e x) = p (target e) - p (source e)) :
    Graph source target → ℝ :=
  Quot.lift (rawPotential source p w) (fun _ _ h => rawPotential_glue source target p w hexact h)

open ComputationalPaths.Path.GeometricTopology

/-- Accumulate actual edge-chart integrals along the user's finite traces. -/
noncomputable def traceChartIntegral (source target : E → V) (w : E → ℝ → ℝ) :
    {a b : Graph source target} → GeometricTrace (edgeStepSystem source target) a b → ℝ
  | _, _, .refl _ => 0
  | _, _, .single e => ∫ x in (0 : ℝ)..1, w e x
  | _, _, .trans t u => traceChartIntegral source target w t + traceChartIntegral source target w u
  | _, _, .symm t => -traceChartIntegral source target w t

/-- Exact edge-chart moments telescope along every actual computational trace. -/
theorem traceChartIntegral_eq_potential_difference (source target : E → V)
    (p : V → ℝ) (w : E → ℝ → ℝ)
    (hexact : ∀ e, (∫ x in (0 : ℝ)..1, w e x) = p (target e) - p (source e))
    {a b : Graph source target} (t : GeometricTrace (edgeStepSystem source target) a b) :
    traceChartIntegral source target w t = graphPotential source target p w hexact b -
      graphPotential source target p w hexact a := by
  induction t with
  | refl a => simp [traceChartIntegral]
  | single e => simpa [traceChartIntegral, graphPotential, edgeStepSystem, vertex, rawPotential] using hexact e
  | trans t u ht hu => simp only [traceChartIntegral, ht, hu]; ring
  | symm t ht => simp only [traceChartIntegral, ht]; ring

end MetricGraphPathPrototype

/-! Analytic time-rescaling lemmas for finite computational traces. The
density is related to realized paths' local edge-coordinate velocity below. -/

namespace MetricGraphTraceDensity

/-- A concatenated density includes the velocities of both half-intervals. -/
noncomputable def concatDensity (f g : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x ≤ 1 / 2 then 2 * f (2 * x) else 2 * g (2 * x - 1)

/-- Reversal changes both the direction and the evaluation point. -/
def reverseDensity (f : ℝ → ℝ) (x : ℝ) : ℝ := -f (1 - x)

theorem concat_right_integral (g : ℝ → ℝ) :
    (∫ x in (1 / 2 : ℝ)..1, 2 * g (2 * x - 1)) = ∫ x in (0 : ℝ)..1, g x := by
  rw [intervalIntegral.integral_const_mul]
  have h := intervalIntegral.smul_integral_comp_mul_add g (a := (1 / 2 : ℝ)) (b := (1 : ℝ)) 2 (-1)
  convert h using 1; norm_num

theorem concat_density_integrable (f g : ℝ → ℝ)
    (hf : IntervalIntegrable f volume 0 1) (hg : IntervalIntegrable g volume 0 1) :
    IntervalIntegrable (concatDensity f g) volume 0 1 := by
  have hl : IntervalIntegrable (fun x : ℝ => 2 * f (2 * x)) volume 0 (1 / 2) := by
    simpa using (hf.comp_mul_left (c := (2 : ℝ))).const_mul 2
  have hr : IntervalIntegrable (fun x : ℝ => 2 * g (2 * x - 1)) volume (1 / 2) 1 := by
    simpa [sub_eq_add_neg] using ((hg.comp_add_right (-1)).comp_mul_left (c := (2 : ℝ))).const_mul 2
  have hdl : IntervalIntegrable (concatDensity f g) volume 0 (1 / 2) := by
    apply hl.congr_uIoo
    intro x hx
    have hx' : x ∈ Ioo (0 : ℝ) (1 / 2) := by simpa only [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hx
    change 2 * f (2 * x) = if x ≤ (1 / 2 : ℝ) then 2 * f (2 * x) else 2 * g (2 * x - 1)
    rw [ite_eq_left (le_of_lt hx'.2)]
  have hdr : IntervalIntegrable (concatDensity f g) volume (1 / 2) 1 := by
    apply hr.congr_uIoo
    intro x hx
    have hx' : x ∈ Ioo (1 / 2 : ℝ) 1 := by simpa only [uIoo_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] using hx
    change 2 * g (2 * x - 1) = if x ≤ (1 / 2 : ℝ) then 2 * f (2 * x) else 2 * g (2 * x - 1)
    rw [ite_eq_right (not_le.mpr hx'.1)]
  exact hdl.trans hdr

theorem concat_density_integral (f g : ℝ → ℝ)
    (hf : IntervalIntegrable f volume 0 1) (hg : IntervalIntegrable g volume 0 1) :
    (∫ x in (0 : ℝ)..1, concatDensity f g x) =
      (∫ x in (0 : ℝ)..1, f x) + ∫ x in (0 : ℝ)..1, g x := by
  have hl : IntervalIntegrable (concatDensity f g) volume 0 (1 / 2) := by
    apply (concat_density_integrable f g hf hg).mono_set
    simp only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2), uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc (by norm_num) (by norm_num)
  have hr : IntervalIntegrable (concatDensity f g) volume (1 / 2) 1 := by
    apply (concat_density_integrable f g hf hg).mono_set
    simp only [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1), uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc (by norm_num) (by norm_num)
  have hs := intervalIntegral.integral_add_adjacent_intervals hl hr
  have hleft : (∫ x in (0 : ℝ)..(1 / 2 : ℝ), concatDensity f g x) =
      ∫ x in (0 : ℝ)..(1 / 2 : ℝ), 2 * f (2 * x) :=
    intervalIntegral.integral_congr_Ioo_of_le (by norm_num) (fun x hx => ite_eq_left (le_of_lt hx.2))
  have hright : (∫ x in (1 / 2 : ℝ)..1, concatDensity f g x) =
      ∫ x in (1 / 2 : ℝ)..1, 2 * g (2 * x - 1) :=
    intervalIntegral.integral_congr_Ioo_of_le (by norm_num) (fun x hx => ite_eq_right (not_le.mpr hx.1))
  have hleft' : (∫ x in (0 : ℝ)..(1 / 2 : ℝ), concatDensity f g x) = ∫ x in (0 : ℝ)..1, f x := by
    rw [hleft, intervalIntegral.integral_const_mul]
    simp
  exact hs.symm.trans (congrArg₂ (fun a b : ℝ => a + b) hleft' (hright.trans (concat_right_integral g)))

theorem reverse_density_integrable (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume 0 1) :
    IntervalIntegrable (reverseDensity f) volume 0 1 := by
  have h : IntervalIntegrable
      (-(fun x : ℝ => f (1 - x))) volume 0 1 := by
    simpa only [sub_zero, sub_self] using ((hf.comp_sub_left (1 : ℝ)).symm.neg)
  apply h.congr
  intro x hx
  rfl

theorem reverse_density_integral (f : ℝ → ℝ) :
    (∫ x in (0 : ℝ)..1, reverseDensity f x) =
      -(∫ x in (0 : ℝ)..1, f x) := by
  change (∫ x in (0 : ℝ)..1, -f (1 - x)) = _
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_comp_sub_left]
  norm_num
end MetricGraphTraceDensity

open MeasureTheory Set
open scoped Interval
open ComputationalPaths.Path.GeometricTopology
open MetricGraphPathPrototype
open MetricGraphTraceDensity

namespace MetricGraphTraceParametric

variable {V E : Type*} [TopologicalSpace V] [TopologicalSpace E]

/-- Time-parametric density for the actual finite computational trace.
The identification with coordinate velocities of its realized path remains a
separate geometric obligation. -/
noncomputable def traceDensity (source target : E → V) (w : E → ℝ → ℝ) :
    {a b : Graph source target} → GeometricTrace (edgeStepSystem source target) a b → ℝ → ℝ
  | _, _, .refl _ => fun _ => 0
  | _, _, .single e => w e
  | _, _, .trans t u => concatDensity (traceDensity source target w t) (traceDensity source target w u)
  | _, _, .symm t => reverseDensity (traceDensity source target w t)

theorem traceDensity_integrable (source target : E → V) (w : E → ℝ → ℝ)
    (hw : ∀ e, IntervalIntegrable (w e) volume 0 1)
    {a b : Graph source target} (t : GeometricTrace (edgeStepSystem source target) a b) :
    IntervalIntegrable (traceDensity source target w t) volume 0 1 := by
  induction t with
  | refl a => simp [traceDensity]
  | single e => exact hw e
  | trans t u ht hu => exact concat_density_integrable _ _ ht hu
  | symm t ht => exact reverse_density_integrable _ ht

theorem traceDensity_integral (source target : E → V) (w : E → ℝ → ℝ)
    (hw : ∀ e, IntervalIntegrable (w e) volume 0 1)
    {a b : Graph source target} (t : GeometricTrace (edgeStepSystem source target) a b) :
    (∫ x in (0 : ℝ)..1, traceDensity source target w t x) = traceChartIntegral source target w t := by
  induction t with
  | refl a => simp [traceDensity, traceChartIntegral]
  | single e => rfl
  | trans t u ht hu =>
    exact (concat_density_integral _ _ (traceDensity_integrable _ _ _ hw t)
      (traceDensity_integrable _ _ _ hw u)).trans (congrArg₂ (fun a b : ℝ => a + b) ht hu)
  | symm t ht => exact (reverse_density_integral _).trans (congrArg (fun z : ℝ => -z) ht)

/-- The single-edge trace follows the quotient edge chart with unit velocity. -/
theorem single_chart (source target : E → V) (w : E → ℝ → ℝ) (e : E)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (GeometricTrace.realize (GeometricTrace.single e :
      GeometricTrace (edgeStepSystem source target)
        (vertex source target (source e)) (vertex source target (target e)))).extend x =
      edgePoint source target e ⟨x, hx⟩ ∧
    traceDensity source target w (GeometricTrace.single e) x = w e x := by
  constructor
  · change (edgePath source target e).extend x = edgePoint source target e ⟨x, hx⟩
    rw [Path.extend_apply _ hx]
    rfl
  · rfl

/-- On the first half, the realized path and its trace density use the same
rescaling, including its velocity factor. -/
theorem trans_chart_left (source target : E → V) (w : E → ℝ → ℝ)
    {a b c : Graph source target}
    (p : GeometricTrace (edgeStepSystem source target) a b)
    (q : GeometricTrace (edgeStepSystem source target) b c)
    (x : ℝ) (hx : x ≤ 1 / 2) :
    (GeometricTrace.realize (.trans p q)).extend x = (GeometricTrace.realize p).extend (2 * x) ∧
    traceDensity source target w (.trans p q) x = 2 * traceDensity source target w p (2 * x) := by
  exact ⟨Path.extend_trans_of_le_half _ _ hx, by simp only [traceDensity, concatDensity, ite_eq_left hx]⟩

/-- The same compatibility holds on the second half. -/
theorem trans_chart_right (source target : E → V) (w : E → ℝ → ℝ)
    {a b c : Graph source target}
    (p : GeometricTrace (edgeStepSystem source target) a b)
    (q : GeometricTrace (edgeStepSystem source target) b c)
    (x : ℝ) (hx : 1 / 2 < x) :
    (GeometricTrace.realize (.trans p q)).extend x = (GeometricTrace.realize q).extend (2 * x - 1) ∧
    traceDensity source target w (.trans p q) x = 2 * traceDensity source target w q (2 * x - 1) := by
  exact ⟨Path.extend_trans_of_half_le _ _ (le_of_lt hx),
    by simp only [traceDensity, concatDensity, ite_eq_right (not_le.mpr hx)]⟩

/-- Reversal reflects the same time parameter in the realized path and density. -/
theorem symm_chart (source target : E → V) (w : E → ℝ → ℝ)
    {a b : Graph source target} (p : GeometricTrace (edgeStepSystem source target) a b)
    (x : ℝ) :
    (GeometricTrace.realize (.symm p)).extend x = (GeometricTrace.realize p).extend (1 - x) ∧
    traceDensity source target w (.symm p) x = -traceDensity source target w p (1 - x) := by
  constructor
  · exact Path.extend_symm_apply _ _
  · rfl

/-- The constant or affine data carried by a local realized trace chart. -/
def TraceLocalData (source target : E → V) (w : E → ℝ → ℝ)
    {a b : Graph source target} (p : GeometricTrace (edgeStepSystem source target) a b)
    (x l r : ℝ) : Prop :=
        ((∃ point, ∀ y ∈ Set.Ioo l r,
            (GeometricTrace.realize p).extend y = point ∧ traceDensity source target w p y = 0) ∨
         (∃ e α β, HasDerivAt (fun y : ℝ => α * y + β) α x ∧
            ∀ y ∈ Set.Ioo l r, ∃ hy : α * y + β ∈ Set.Icc (0 : ℝ) 1,
              (GeometricTrace.realize p).extend y = edgePoint source target e ⟨α * y + β, hy⟩ ∧
              traceDensity source target w p y = α * w e (α * y + β)))

/-- The trace has a constant or affine edge chart on a neighborhood. -/
def TraceLocalVelocity (source target : E → V) (w : E → ℝ → ℝ)
    {a b : Graph source target} (p : GeometricTrace (edgeStepSystem source target) a b)
    (x : ℝ) : Prop :=
  ∃ l r : ℝ, 0 ≤ l ∧ l < x ∧ x < r ∧ r ≤ 1 ∧ TraceLocalData source target w p x l r

/-- Realized path and density agree with an affine doubling on an open half. -/
def TraceChartTransport (source target : E → V) (w : E → ℝ → ℝ)
    {a b c d : Graph source target}
    (p : GeometricTrace (edgeStepSystem source target) a b)
    (q : GeometricTrace (edgeStepSystem source target) c d) (δ : ℝ) : Prop :=
  ∀ y ∈ Set.Ioo (δ / 2) ((δ + 1) / 2),
    (GeometricTrace.realize q).extend y = (GeometricTrace.realize p).extend (2 * y - δ) ∧
    traceDensity source target w q y = 2 * traceDensity source target w p (2 * y - δ)

theorem double_shift_mem {l r c y : ℝ} (hy : y ∈ Set.Ioo ((l + c) / 2) ((r + c) / 2)) :
    2 * y - c ∈ Set.Ioo l r := by constructor <;> linarith [hy.1, hy.2]

theorem affine_chart_coordinate (s t α β y : ℝ) :
    (s * α) * y + (α * t + β) = α * (s * y + t) + β := by ring

/-- Transport actual trace data along a chart with an affine parameter. -/
theorem traceLocalData_affine (source target : E → V) (w : E → ℝ → ℝ)
    {a b c d : Graph source target}
    (p : GeometricTrace (edgeStepSystem source target) a b)
    (q : GeometricTrace (edgeStepSystem source target) c d)
    (s t x l r L R : ℝ)
    (hmap : ∀ y ∈ Set.Ioo L R, s * y + t ∈ Set.Ioo l r)
    (hchart : ∀ y ∈ Set.Ioo L R,
      (GeometricTrace.realize q).extend y = (GeometricTrace.realize p).extend (s * y + t) ∧
      traceDensity source target w q y = s * traceDensity source target w p (s * y + t))
    (h : TraceLocalData source target w p (s * x + t) l r) :
    TraceLocalData source target w q x L R :=
  h.elim
    (fun ⟨point, hp⟩ => Or.inl ⟨point, fun y hy =>
      let ⟨hp0, hpd⟩ := hp (s * y + t) (hmap y hy)
      let ⟨hq0, hqd⟩ := hchart y hy
      ⟨hq0.trans hp0, hqd.trans ((congrArg (fun z => s * z) hpd).trans (mul_zero s))⟩⟩)
    (fun ⟨e, α, β, _, hp⟩ => Or.inr ⟨e, s * α, α * t + β,
      (hasDerivAt_const_mul (x := x) (s * α)).add_const (α * t + β),
      fun y hy =>
        let ⟨hu, hp0, hpd⟩ := hp (s * y + t) (hmap y hy)
        let ⟨hq0, hqd⟩ := hchart y hy
        let hu' := (affine_chart_coordinate s t α β y).symm ▸ hu
        ⟨hu', by simpa only [affine_chart_coordinate] using hq0.trans hp0,
          hqd.trans ((congrArg (fun z => s * z) hpd).trans
            ((mul_assoc s α _).symm.trans
              (congrArg (fun z => (s * α) * w e z) (affine_chart_coordinate s t α β y).symm)))⟩⟩)

/-- Transport a local chart through an affine doubling on an open half. -/
theorem traceLocalVelocity_double_shift (source target : E → V) (w : E → ℝ → ℝ)
    {a b c d : Graph source target}
    (p : GeometricTrace (edgeStepSystem source target) a b)
    (q : GeometricTrace (edgeStepSystem source target) c d) (δ x : ℝ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hchart : TraceChartTransport source target w p q δ)
    (h : TraceLocalVelocity source target w p (2 * x - δ)) :
    TraceLocalVelocity source target w q x := by
  unfold TraceLocalVelocity at h ⊢
  obtain ⟨l, r, hl0, hlx, hxr, hr1, hc⟩ := h
  refine ⟨(l + δ) / 2, (r + δ) / 2, by linarith, by linarith,
    by linarith, by linarith, ?_⟩
  apply traceLocalData_affine source target w p q 2 (-δ) x l r
  · intro y hy
    simpa only [sub_eq_add_neg] using double_shift_mem hy
  · intro y hy
    simpa only [sub_eq_add_neg] using hchart y ⟨by linarith [hy.1], by linarith [hy.2]⟩
  · simpa only [sub_eq_add_neg] using hc

/-- Reversing a local trace chart reverses its parameter and velocity. -/
theorem traceLocalVelocity_symm (source target : E → V) (w : E → ℝ → ℝ)
    {a b : Graph source target} (p : GeometricTrace (edgeStepSystem source target) a b)
    (x : ℝ) (h : TraceLocalVelocity source target w p (1 - x)) :
    TraceLocalVelocity source target w (.symm p) x := by
  unfold TraceLocalVelocity at h ⊢
  obtain ⟨l, r, hl0, hlx, hxr, hr1, hc⟩ := h
  refine ⟨1 - r, 1 - l, by linarith, by linarith, by linarith, by linarith, ?_⟩
  apply traceLocalData_affine source target w p (.symm p) (-1) 1 x l r
  · intro y hy
    simp only [neg_one_mul, neg_add_eq_sub]
    exact ⟨by linarith [hy.2], by linarith [hy.1]⟩
  · intro y hy
    simpa only [neg_one_mul, neg_add_eq_sub] using symm_chart source target w p y
  · simpa only [neg_one_mul, neg_add_eq_sub] using hc

theorem traceLocalVelocity_of_irrational (source target : E → V) (w : E → ℝ → ℝ)
    {a b : Graph source target} (p : GeometricTrace (edgeStepSystem source target) a b)
    (x : ℝ) (hbreak : Irrational x) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    TraceLocalVelocity source target w p x := by
  exact GeometricTrace.rec
    (motive := fun _ _ p => ∀ x, Irrational x → x ∈ Set.Ioo (0 : ℝ) 1 →
      TraceLocalVelocity source target w p x)
    (fun a x _ hx => ⟨0, 1, le_rfl, hx.1, hx.2, le_rfl, Or.inl ⟨a, by
      intro y hy
      simp [GeometricTrace.realize, traceDensity]⟩⟩)
    (fun e x _ hx => ⟨0, 1, le_rfl, hx.1, hx.2, le_rfl, Or.inr ⟨e, 1, 0,
      by simpa using (hasDerivAt_const_mul (x := x) (1 : ℝ)).add_const 0,
      fun y hy => by
        have hunit : y ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hy.1, le_of_lt hy.2⟩
        have h := single_chart source target w e y hunit
        exact ⟨by simpa using hunit, by simpa using h.1, by simpa using h.2⟩⟩⟩)
    (fun {a b c} p q hp hq x hbreak hx => by
      have hne : x ≠ (1 / 2 : ℝ) := by simpa using hbreak.ne_rat (1 / 2 : ℚ)
      rcases lt_or_gt_of_ne hne with hleft | hright
      · refine traceLocalVelocity_double_shift source target w p (.trans p q) 0 x
          (by norm_num) (by norm_num) ?_ ?_
        · intro y hy
          simpa using trans_chart_left source target w p q y (by linarith [hy.2])
        · simpa using hp (2 * x) (by simpa using hbreak.natCast_mul (m := 2) (by norm_num))
            ⟨by linarith [hx.1], by linarith⟩
      · refine traceLocalVelocity_double_shift source target w q (.trans p q) 1 x
          (by norm_num) (by norm_num) ?_ ?_
        · intro y hy
          simpa using trans_chart_right source target w p q y (by linarith [hy.1])
        · exact hq (2 * x - 1) (by simpa using (hbreak.natCast_mul (m := 2) (by norm_num)).sub_natCast 1)
            ⟨by linarith, by linarith [hx.2]⟩)
    (fun {a b} p hp x hbreak hx => traceLocalVelocity_symm source target w p x
      (hp (1 - x) (by simpa using hbreak.natCast_sub 1)
        ⟨by linarith [hx.2], by linarith [hx.1]⟩)) p x hbreak hx

/-- Almost every interior time has the actual local chart and velocity
interpretation of the trace density. -/
theorem realizedTrace_ae_local_velocity (source target : E → V) (w : E → ℝ → ℝ)
    {a b : Graph source target} (p : GeometricTrace (edgeStepSystem source target) a b) :
    ∀ᵐ x : ℝ ∂volume, x ∈ Set.Ioo (0 : ℝ) 1 →
      ∃ l r : ℝ, 0 ≤ l ∧ l < x ∧ x < r ∧ r ≤ 1 ∧
        ((∃ point, ∀ y ∈ Set.Ioo l r,
            (GeometricTrace.realize p).extend y = point ∧ traceDensity source target w p y = 0) ∨
         (∃ e α β, HasDerivAt (fun y : ℝ => α * y + β) α x ∧
            ∀ y ∈ Set.Ioo l r, ∃ hy : α * y + β ∈ Set.Icc (0 : ℝ) 1,
              (GeometricTrace.realize p).extend y = edgePoint source target e ⟨α * y + β, hy⟩ ∧
              traceDensity source target w p y = α * w e (α * y + β))) := by
  have havoid : ∀ᵐ x : ℝ ∂volume, Irrational x := by
    simpa [Irrational] using
      (Set.countable_range (fun q : ℚ => (q : ℝ))).ae_notMem volume
  filter_upwards [havoid] with x hbreak
  intro hx
  exact traceLocalVelocity_of_irrational source target w p x hbreak hx

/-- An undirected combinatorial reachability proof gives an actual finite
computational trace between the corresponding quotient vertices. -/
theorem exists_vertex_trace (source target : E → V) {a b : V}
    (h : Relation.EqvGen (fun x y => ∃ e, source e = x ∧ target e = y) a b) :
    Nonempty (GeometricTrace (edgeStepSystem source target)
      (vertex source target a) (vertex source target b)) := by
  induction h with
  | rel x y he =>
    obtain ⟨e, hx, hy⟩ := he
    subst x
    subst y
    exact ⟨.single e⟩
  | refl x => exact ⟨.refl (vertex source target x)⟩
  | symm x y h ih =>
    obtain ⟨t⟩ := ih
    exact ⟨.symm t⟩
  | trans x y z h1 h2 ih1 ih2 =>
    obtain ⟨t⟩ := ih1
    obtain ⟨u⟩ := ih2
    exact ⟨.trans t u⟩

/-- For connected vertex graphs, vanishing of the realized trace-density
integral on every closed finite trace is equivalent to exact edge moments. -/
theorem closed_trace_integrals_iff_exact_moments (source target : E → V) (root : V)
    (connected : ∀ a b, Relation.EqvGen (fun x y => ∃ e, source e = x ∧ target e = y) a b)
    (w : E → ℝ → ℝ) (hw : ∀ e, IntervalIntegrable (w e) volume 0 1) :
    (∀ {a : Graph source target} (t : GeometricTrace (edgeStepSystem source target) a a),
      (∫ x in (0 : ℝ)..1, traceDensity source target w t x) = 0) ↔
    ∃ p : V → ℝ, ∀ e, (∫ x in (0 : ℝ)..1, w e x) = p (target e) - p (source e) := by
  classical
  constructor
  · intro hclosed
    let paths (v : V) : GeometricTrace (edgeStepSystem source target)
        (vertex source target root) (vertex source target v) :=
      Classical.choice (exists_vertex_trace source target (connected root v))
    let p : V → ℝ := fun v => traceChartIntegral source target w (paths v)
    refine ⟨p, ?_⟩
    intro e
    let loop : GeometricTrace (edgeStepSystem source target)
        (vertex source target root) (vertex source target root) :=
      .trans (.trans (paths (source e)) (.single e)) (.symm (paths (target e)))
    have hz : traceChartIntegral source target w loop = 0 :=
      (traceDensity_integral source target w hw loop).symm.trans (hclosed loop)
    change p (source e) + (∫ x in (0 : ℝ)..1, w e x) + -p (target e) = 0 at hz
    linarith
  · rintro ⟨p, hexact⟩ a t
    exact (traceDensity_integral source target w hw t).trans
      ((traceChartIntegral_eq_potential_difference source target p w hexact t).trans (sub_self _))
end MetricGraphTraceParametric

namespace MetricGraphTraceParametric

variable {V E : Type*} [TopologicalSpace V] [TopologicalSpace E]
open Finset

/-- The forced metric-graph interval system is solvable exactly when cosine
balance holds and the sine-weighted density integral vanishes on every
closed finite computational trace of the glued graph. -/
theorem forced_interval_iff_closed_trace_integrals
    [Fintype V] [Fintype E] [DecidableEq V]
    (source target : E → V) (root : V)
    (connected : ∀ a b, Relation.EqvGen (fun x y => ∃ e, source e = x ∧ target e = y) a b)
    (f : E → ℝ → ℝ) (hf : ∀ e, ContinuousOn (f e) (Set.Icc 0 1))
    (k : ℝ) (hk : k ≠ 0) (hs : Real.sin k = 0) (hc : Real.cos k = 1) :
    MetricGraphResonancePrototype.intervalGraphSolution source target f k ↔
      ((∑ e, ∫ t in (0 : ℝ)..1, f e t * Real.cos (k * t)) = 0 ∧
        ∀ {a : Graph source target} (trace : GeometricTrace (edgeStepSystem source target) a a),
          (∫ x in (0 : ℝ)..1, traceDensity source target
            (fun e t => f e t * Real.sin (k * t)) trace x) = 0) := by
  have hscont : Continuous (fun t : ℝ => Real.sin (k * t)) := by fun_prop
  have hw : ∀ e, IntervalIntegrable (fun t => f e t * Real.sin (k * t)) volume 0 1 :=
    fun e => ((hf e).mul hscont.continuousOn).intervalIntegrable_of_Icc (by norm_num)
  have htrace := closed_trace_integrals_iff_exact_moments source target root connected
    (fun e t => f e t * Real.sin (k * t)) hw
  have hsolution := MetricGraphResonancePrototype.forced_connected_graph_interval_iff
    source target root connected f hf k hk hs hc
  change MetricGraphResonancePrototype.intervalGraphSolution source target f k ↔
    ((∑ e, ∫ t in (0 : ℝ)..1, f e t * Real.cos (k * t)) = 0 ∧
      ∃ p : V → ℝ, ∀ e, (∫ t in (0 : ℝ)..1, f e t * Real.sin (k * t)) =
        p (target e) - p (source e)) at hsolution
  exact hsolution.trans (and_congr_right (fun _ => htrace.symm))
end MetricGraphTraceParametric

namespace MetricGraphResonancePrototype
/-- A full-period sine/cosine pairing is zero. -/
theorem full_period_sine_cosine_zero (k : ℝ) (hk : k ≠ 0) (hs : Real.sin k = 0) :
    (∫ t in (0 : ℝ)..1, Real.sin (k * t) * Real.cos (k * t)) = 0 := by
  have h := intervalIntegral.integral_comp_mul_left
    (a := (0 : ℝ)) (b := 1) (fun t : ℝ => Real.sin t * Real.cos t) hk
  simpa [integral_sin_mul_cos₁, hs] using h

noncomputable def thetaForce (e : Fin 3) (t : ℝ) : ℝ :=
  if e = 0 then Real.sin (2 * Real.pi * t) else 0

/-- The branched forcing satisfies the scalar cosine balance. -/
theorem theta_cosine_balance :
    (∑ e : Fin 3, ∫ t in (0 : ℝ)..1,
      thetaForce e t * Real.cos (2 * Real.pi * t)) = 0 := by
  have hk : (2 : ℝ) * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hz := full_period_sine_cosine_zero (2 * Real.pi) hk Real.sin_two_pi
  simp [Fin.sum_univ_succ, thetaForce, hz]

/-- Even with scalar balance, three parallel edges cannot share both
    endpoint values under this forcing. -/
theorem theta_forcing_obstruction (u q : Fin 3 → ℝ → ℝ)
    (huc : ∀ e, ContinuousOn (u e) (Icc 0 1))
    (hqc : ∀ e, ContinuousOn (q e) (Icc 0 1))
    (hu : ∀ e x, x ∈ Set.Ioo 0 1 → HasDerivAt (u e) (q e x) x)
    (hq : ∀ e x, x ∈ Set.Ioo 0 1 → HasDerivAt (q e)
      (-((2 * Real.pi) ^ 2 * u e x + thetaForce e x)) x)
    (h0 : u 0 0 = u 1 0) (h1 : u 0 1 = u 1 1) : False := by
  have hf : ∀ e, ContinuousOn (thetaForce e) (Icc 0 1) := by
    intro e
    unfold thetaForce
    split_ifs <;> fun_prop
  have hm0 := sine_moment_identity_interval (u 0) (q 0) (thetaForce 0) (2 * Real.pi)
    (huc 0) (hqc 0) (hu 0) (hq 0) (hf 0) Real.sin_two_pi Real.cos_two_pi
  have hm1 := sine_moment_identity_interval (u 1) (q 1) (thetaForce 1) (2 * Real.pi)
    (huc 1) (hqc 1) (hu 1) (hq 1) (hf 1) Real.sin_two_pi Real.cos_two_pi
  rw [h0, h1] at hm0
  have hsame := hm0.trans hm1.symm
  simp [thetaForce] at hsame
  have hsq : (∫ t in (0 : ℝ)..1, (Real.sin (2 * Real.pi * t)) ^ 2) = 0 := by
    simpa only [pow_two] using hsame
  linarith [sin_squared_positive]

end MetricGraphResonancePrototype

