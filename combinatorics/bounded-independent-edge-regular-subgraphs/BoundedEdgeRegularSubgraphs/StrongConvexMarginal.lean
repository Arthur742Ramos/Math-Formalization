module

public import BoundedEdgeRegularSubgraphs.GaussianMarginalDensity
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# A coordinate tail bound from a convex tilted potential
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace BoundedEdgeRegularSubgraphs

/-- The mass outside a coordinate interval is bounded by its Gaussian
tail factor times the total mass. The convexity condition is imposed on
the tilted potential restricted to the support. -/
theorem integral_coordinate_tail_le_of_convex_tilt {ι : Type*} [Fintype ι]
    (D : Set (ℝ × (ι → ℝ))) (hD : MeasurableSet D) (V : ℝ × (ι → ℝ) → ℝ)
    (hV : Measurable V) {κ r : ℝ} (hκ : 0 ≤ κ) (hr : 0 ≤ r)
    (hconv : ConvexOn ℝ D (fun p ↦ V p - κ * p.1 ^ 2 / 2))
    (hDneg : ∀ p, -p ∈ D ↔ p ∈ D) (hVneg : ∀ p ∈ D, V (-p) = V p)
    (hI : Integrable (D.indicator (fun p ↦ Real.exp (-V p))) volume)
    (hIslice : ∀ t : ℝ, Integrable (fun x ↦ D.indicator (fun p ↦ Real.exp (-V p)) (t, x))) :
    (∫ p in D ∩ {p | r < |p.1|}, Real.exp (-V p)) ≤
      Real.exp (-κ * r ^ 2 / 2) * ∫ p in D, Real.exp (-V p) := by
  let W (p : ℝ × (ι → ℝ)) := V p - κ * p.1 ^ 2 / 2
  let f (p : ℝ × (ι → ℝ)) := D.indicator (fun p ↦ Real.exp (-V p)) p
  let F (t : ℝ) (x : ι → ℝ) := ENNReal.ofReal (D.indicator (fun p ↦ Real.exp (-W p)) (t, x))
  let g (t : ℝ) := ∫ x, f (t, x)
  have hW : Measurable W := hV.sub (measurable_const.mul (measurable_fst.pow_const 2) |>.div_const 2)
  have hWneg (p : ℝ × (ι → ℝ)) (hp : p ∈ D) : W (-p) = W p := by
    simp only [W, Prod.fst_neg, neg_sq, hVneg p hp]
  have hF (t : ℝ) : Measurable (F t) :=
    (ENNReal.measurable_ofReal.comp ((Real.measurable_exp.comp hW.neg).indicator hD)).comp
      (measurable_const.prodMk measurable_id)
  have heval (t : ℝ) (x : ι → ℝ) : F t x =
      ENNReal.ofReal (Real.exp (κ * t ^ 2 / 2) * f (t, x)) := by
    by_cases hx : (t, x) ∈ D
    · simp only [F, f, W, indicator_of_mem hx]
      rw [← Real.exp_add]
      congr 2
      ring
    · simp [F, f, hx]
  have hi (t : ℝ) : Integrable (fun x ↦ Real.exp (κ * t ^ 2 / 2) * f (t, x)) :=
    (hIslice t).const_mul _
  have hfin (t : ℝ) : (∫⁻ x, F t x) ≠ ∞ := by
    have hh (x : ι → ℝ) : F t x = ‖Real.exp (κ * t ^ 2 / 2) * f (t, x)‖ₑ :=
      (heval t x).trans (Real.enorm_eq_ofReal (mul_nonneg (Real.exp_nonneg _)
        (indicator_nonneg (fun p _ ↦ Real.exp_nonneg (-V p)) (t, x)))).symm
    simp_rw [hh]
    exact (hi t).hasFiniteIntegral.ne
  have hG (t : ℝ) : (∫⁻ x, F t x).toReal = Real.exp (κ * t ^ 2 / 2) * g t := by
    simp_rw [heval]
    rw [← integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ (fun x ↦ mul_nonneg (Real.exp_nonneg _)
        (indicator_nonneg (fun p _ ↦ Real.exp_nonneg (-V p)) (t, x))))
      (hi t).aestronglyMeasurable, integral_const_mul]
  have hshape (t s a : ℝ) (ha : 0 < a) (ha₁ : a < 1) (u v : ι → ℝ) :
      F t u ^ a * F s v ^ (1 - a) ≤ F (a * t + (1 - a) * s) (a • u + (1 - a) • v) := by
    by_cases hu : (t, u) ∈ D
    swap
    · simp [F, hu, ENNReal.zero_rpow_of_pos ha]
    by_cases hv : (s, v) ∈ D
    swap
    · simp [F, hv, ENNReal.zero_rpow_of_pos (sub_pos.mpr ha₁)]
    have hz := hconv.1 hu hv ha.le (sub_nonneg.mpr ha₁.le) (by ring : a + (1 - a) = 1)
    have h := hconv.2 hu hv ha.le (sub_nonneg.mpr ha₁.le) (by ring : a + (1 - a) = 1)
    change (a * t + (1 - a) * s, a • u + (1 - a) • v) ∈ D at hz
    change W (a * t + (1 - a) * s, a • u + (1 - a) • v) ≤
      a * W (t, u) + (1 - a) * W (s, v) at h
    simp only [F, indicator_of_mem hu, indicator_of_mem hv, indicator_of_mem hz]
    rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),
      ← Real.exp_mul, ← Real.exp_mul, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith only [h]))
  have hFneg (t : ℝ) (x : ι → ℝ) : F (-t) (-x) = F t x := by
    have h := hDneg (t, x)
    change (-t, -x) ∈ D ↔ (t, x) ∈ D at h
    by_cases hx : (t, x) ∈ D
    · simp only [F, indicator_of_mem hx, indicator_of_mem (h.mpr hx)]
      exact congrArg (fun y ↦ ENNReal.ofReal (Real.exp (-y))) (hWneg (t, x) hx)
    · have hx' : (-t, -x) ∉ D := fun hz ↦ hx (h.mp hz)
      simp [F, hx, hx']
  have hGneg := even_lintegral_of_joint_even F hF hFneg
  simp_rw [hG, neg_sq] at hGneg
  have hge (t : ℝ) : g (-t) = g t :=
    mul_left_cancel₀ (Real.exp_ne_zero _) (hGneg t)
  have hGconv := convex_superlevel_lintegral_of_joint_logConcave F hF hfin hshape
  simp_rw [hG] at hGconv
  have htail := integral_abs_tail_le_of_gaussian_tilt_antitone g hI.integral_prod_left
    (fun t ↦ integral_nonneg (fun x ↦ indicator_nonneg (fun p _ ↦ Real.exp_nonneg (-V p)) (t, x)))
    hge hκ hr (antitoneOn_nonneg_of_even_convex_superlevel _
      (fun t ↦ by rw [neg_sq, hge]) hGconv)
  let B := {t : ℝ | r < |t|}
  have hB : MeasurableSet B := measurableSet_lt measurable_const continuous_abs.measurable
  have hsnd : (∫ p in D, Real.exp (-V p)) = ∫ t, g t := by
    rw [← integral_indicator hD]
    exact integral_prod f hI
  have hfst : (∫ p in D ∩ {p | r < |p.1|}, Real.exp (-V p)) = ∫ t in B, g t := by
    change (∫ p in D ∩ Prod.fst ⁻¹' B, Real.exp (-V p)) = _
    rw [← integral_indicator (hD.inter (measurable_fst hB)), ← integral_indicator hB]
    have hh : (D ∩ Prod.fst ⁻¹' B).indicator (fun p ↦ Real.exp (-V p)) =
        (Prod.fst ⁻¹' B).indicator f := by
      funext p
      by_cases h₁ : p ∈ D <;> by_cases h₂ : p.1 ∈ B <;> simp [f, h₁, h₂]
    rw [hh]
    have hi' : Integrable ((Prod.fst ⁻¹' B).indicator f)
        ((volume : Measure ℝ).prod (volume : Measure (ι → ℝ))) :=
      hI.indicator (measurable_fst hB)
    change (∫ p, (Prod.fst ⁻¹' B).indicator f p ∂(volume.prod volume)) = _
    rw [integral_prod _ hi']
    congr 1
    funext t
    by_cases ht : t ∈ B
    · rw [indicator_of_mem ht]
      exact integral_congr_ae (ae_of_all _ (fun x ↦
        indicator_of_mem (show (t, x) ∈ Prod.fst ⁻¹' B from ht) _))
    · rw [indicator_of_notMem ht]
      have hzero : (fun x : ι → ℝ ↦ (Prod.fst ⁻¹' B).indicator f (t, x)) = fun _ ↦ 0 :=
        funext (fun x ↦ indicator_of_notMem (show (t, x) ∉ Prod.fst ⁻¹' B from ht) _)
      rw [hzero, integral_zero]
  rw [hfst, hsnd]
  exact htail

end BoundedEdgeRegularSubgraphs
