/-
Copyright (c) 2026. Released under the BSD-3-Clause license.

The sharp variance estimate for a Lipschitz closed loop. The proof uses the
cubic primitive of the nonnegative range weight, actual absolute continuity,
and the two arcs between an attained minimum and maximum.
-/
module

public import ErdosOverlap.ContinuousDual
public import Mathlib.Topology.Order.Compact

open MeasureTheory Set

namespace ErdosOverlap

public section

noncomputable section

@[expose] def varianceWeight (R y : ℝ) : ℝ := R ^ 2 - y ^ 2

@[expose] def variancePrimitive (R y : ℝ) : ℝ := R ^ 2 * y - y ^ 3 / 3

theorem varianceWeight_nonneg {R y : ℝ} (hy : |y| ≤ R) :
    0 ≤ varianceWeight R y := by
  have h := abs_le.mp hy
  have hp := mul_nonneg (by linarith : 0 ≤ R - y) (by linarith : 0 ≤ R + y)
  dsimp [varianceWeight]
  nlinarith

theorem variancePrimitive_absolutelyContinuous {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (R : ℝ) :
    AbsolutelyContinuousOnInterval (fun t => variancePrimitive R (f t)) a b := by
  have hcube := (hf.mul hf).mul hf
  have h := (hf.const_mul (R ^ 2)).sub (hcube.const_mul (1 / 3))
  convert! h using 1
  funext t
  simp only [variancePrimitive, Pi.sub_apply, Pi.mul_apply]
  ring

/-- The required polynomial chain rule and fundamental theorem hold for
absolutely continuous functions, with no differentiability at every point. -/
theorem integral_varianceWeight_mul_deriv {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (R : ℝ) :
    (∫ t in a..b, varianceWeight R (f t) * deriv f t) =
      variancePrimitive R (f b) - variancePrimitive R (f a) := by
  have hF := variancePrimitive_absolutelyContinuous hf R
  have heq : ∀ᵐ t ∂volume, t ∈ uIcc a b →
      deriv (fun x => variancePrimitive R (f x)) t =
        varianceWeight R (f t) * deriv f t := by
    filter_upwards [hf.ae_differentiableAt] with t ht
    intro hti
    have hd := (ht hti).hasDerivAt
    have hp := (hd.const_mul (R ^ 2)).sub (((hd.mul hd).mul hd).div_const 3)
    have hp' : HasDerivAt (fun x => variancePrimitive R (f x))
        (varianceWeight R (f t) * deriv f t) t := by
      convert! hp using 1 <;> simp only [variancePrimitive, varianceWeight, Pi.mul_apply]
      all_goals first | (funext x; simp only [Pi.sub_apply]; ring) | ring
    exact hp'.deriv
  calc
    _ = ∫ t in a..b, deriv (fun x => variancePrimitive R (f x)) t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [heq] with t ht
      intro hti
      exact (ht (uIoc_subset_uIcc hti)).symm
    _ = _ := hF.integral_deriv_eq_sub

theorem closedLoop_abs_deriv_le {f : ℝ → ℝ} {a : ℝ} {L : NNReal}
    (hf : LipschitzOnWith L f (uIcc (0 : ℝ) a))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) a) : |deriv f t| ≤ L := by
  have ha : (0 : ℝ) ≤ a := by linarith [ht.1, ht.2]
  have hmem : uIcc (0 : ℝ) a ∈ nhds t := by
    rw [uIcc_of_le ha]
    exact Icc_mem_nhds ht.1 ht.2
  simpa only [Real.norm_eq_abs] using norm_deriv_le_of_lipschitzOn hmem hf

/-- A weighted primitive increment is paid for by the Lipschitz budget on
any subinterval. -/
theorem variancePrimitive_increment_bound
    {f : ℝ → ℝ} {a R u v : ℝ} {L : NNReal}
    (ha : 0 ≤ a) (hf : LipschitzOnWith L f (uIcc (0 : ℝ) a))
    (hbox : ∀ t ∈ Icc (0 : ℝ) a, |f t| ≤ R)
    (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ a) :
    |variancePrimitive R (f v) - variancePrimitive R (f u)| ≤
      (L : ℝ) * ∫ t in u..v, varianceWeight R (f t) := by
  have hsub : uIcc u v ⊆ uIcc (0 : ℝ) a := by
    rw [uIcc_of_le huv, uIcc_of_le ha]
    intro t ht
    exact ⟨hu.trans ht.1, ht.2.trans hv⟩
  have hac := (hf.mono hsub).absolutelyContinuousOnInterval
  have hw : ContinuousOn (fun t => varianceWeight R (f t)) (uIcc u v) :=
    continuousOn_const.sub (hac.continuousOn.pow 2)
  have hp : IntervalIntegrable
      (fun t => varianceWeight R (f t) * deriv f t) volume u v :=
    hac.intervalIntegrable_deriv.continuousOn_mul hw
  have hupper : IntervalIntegrable
      (fun t => (L : ℝ) * varianceWeight R (f t)) volume u v :=
    hw.intervalIntegrable.const_mul (L : ℝ)
  rw [← integral_varianceWeight_mul_deriv hac R]
  change ‖∫ t in u..v, varianceWeight R (f t) * deriv f t‖ ≤ _
  calc
    _ ≤ ∫ t in u..v, ‖varianceWeight R (f t) * deriv f t‖ :=
      intervalIntegral.norm_integral_le_integral_norm huv
    _ ≤ ∫ t in u..v, (L : ℝ) * varianceWeight R (f t) := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo huv hp.norm hupper
      intro t ht
      have hti : t ∈ Ioo (0 : ℝ) a :=
        ⟨lt_of_le_of_lt hu ht.1, lt_of_lt_of_le ht.2 hv⟩
      have hw0 := varianceWeight_nonneg (hbox t ⟨le_of_lt hti.1, le_of_lt hti.2⟩)
      have hd := closedLoop_abs_deriv_le hf hti
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw0]
      nlinarith
    _ = _ := intervalIntegral.integral_const_mul _ _

/-- Both arcs of a closed loop contribute to the primitive increment. -/
theorem closedLoop_weight_lower_ordered
    {f : ℝ → ℝ} {a R u v : ℝ} {L : NNReal}
    (ha : 0 ≤ a) (hf : LipschitzOnWith L f (uIcc (0 : ℝ) a))
    (hperiod : f 0 = f a)
    (hbox : ∀ t ∈ Icc (0 : ℝ) a, |f t| ≤ R)
    (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ a) :
    2 * |variancePrimitive R (f v) - variancePrimitive R (f u)| ≤
      (L : ℝ) * ∫ t in (0 : ℝ)..a, varianceWeight R (f t) := by
  have h₁ := variancePrimitive_increment_bound ha hf hbox le_rfl hu (huv.trans hv)
  have h₂ := variancePrimitive_increment_bound ha hf hbox hu huv hv
  have h₃ := variancePrimitive_increment_bound ha hf hbox (hu.trans huv) hv le_rfl
  have htriangle : |variancePrimitive R (f v) - variancePrimitive R (f u)| ≤
      |variancePrimitive R (f u) - variancePrimitive R (f 0)| +
      |variancePrimitive R (f a) - variancePrimitive R (f v)| := by
    calc
      _ ≤ |variancePrimitive R (f v) - variancePrimitive R (f 0)| +
          |variancePrimitive R (f 0) - variancePrimitive R (f u)| := abs_sub_le _ _ _
      _ = _ := by
        rw [abs_sub_comm (variancePrimitive R (f v)) (variancePrimitive R (f 0)),
          abs_sub_comm (variancePrimitive R (f 0)) (variancePrimitive R (f u))]
        rw [hperiod]
        ring
  have hw : ContinuousOn (fun t => varianceWeight R (f t)) (uIcc (0 : ℝ) a) :=
    continuousOn_const.sub (hf.continuousOn.pow 2)
  have hui : u ∈ uIcc (0 : ℝ) a := by
    rw [uIcc_of_le ha]
    exact ⟨hu, huv.trans hv⟩
  have hvi : v ∈ uIcc (0 : ℝ) a := by
    rw [uIcc_of_le ha]
    exact ⟨hu.trans huv, hv⟩
  have h01 := (hw.mono (uIcc_subset_uIcc (left_mem_uIcc) hui)).intervalIntegrable (μ := volume)
  have h12 := (hw.mono (uIcc_subset_uIcc hui hvi)).intervalIntegrable (μ := volume)
  have h23 := (hw.mono (uIcc_subset_uIcc hvi (right_mem_uIcc))).intervalIntegrable (μ := volume)
  have hadd₁ := intervalIntegral.integral_add_adjacent_intervals h01 h12
  have hadd₂ := intervalIntegral.integral_add_adjacent_intervals (h01.trans h12) h23
  have hsum : (L : ℝ) * (∫ t in (0 : ℝ)..u, varianceWeight R (f t)) +
      (L : ℝ) * (∫ t in u..v, varianceWeight R (f t)) +
      (L : ℝ) * (∫ t in v..a, varianceWeight R (f t)) =
      (L : ℝ) * (∫ t in (0 : ℝ)..a, varianceWeight R (f t)) := by
    rw [← mul_add, ← mul_add, hadd₁, hadd₂]
  linarith

theorem closedLoop_weight_lower
    {f : ℝ → ℝ} {a R u v : ℝ} {L : NNReal}
    (ha : 0 ≤ a) (hf : LipschitzOnWith L f (uIcc (0 : ℝ) a))
    (hperiod : f 0 = f a)
    (hbox : ∀ t ∈ Icc (0 : ℝ) a, |f t| ≤ R)
    (hu : u ∈ Icc (0 : ℝ) a) (hv : v ∈ Icc (0 : ℝ) a) :
    2 * |variancePrimitive R (f v) - variancePrimitive R (f u)| ≤
      (L : ℝ) * ∫ t in (0 : ℝ)..a, varianceWeight R (f t) := by
  rcases le_total u v with huv | hvu
  · exact closedLoop_weight_lower_ordered ha hf hperiod hbox hu.1 huv hv.2
  · rw [abs_sub_comm]
    exact closedLoop_weight_lower_ordered ha hf hperiod hbox hv.1 hvu hu.2

theorem closedLoop_range_le_ordered
    {f : ℝ → ℝ} {a u v : ℝ} {L : NNReal}
    (ha : 0 ≤ a) (hf : LipschitzOnWith L f (uIcc (0 : ℝ) a))
    (hperiod : f 0 = f a) (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ a) :
    |f v - f u| ≤ (L : ℝ) * a / 2 := by
  have h0 : (0 : ℝ) ∈ uIcc (0 : ℝ) a := left_mem_uIcc
  have ha' : a ∈ uIcc (0 : ℝ) a := right_mem_uIcc
  have hui : u ∈ uIcc (0 : ℝ) a := by
    rw [uIcc_of_le ha]
    exact ⟨hu, huv.trans hv⟩
  have hvi : v ∈ uIcc (0 : ℝ) a := by
    rw [uIcc_of_le ha]
    exact ⟨hu.trans huv, hv⟩
  have hinner := hf.dist_le_mul v hvi u hui
  have hleft := hf.dist_le_mul u hui 0 h0
  have hright := hf.dist_le_mul a ha' v hvi
  simp only [Real.dist_eq, sub_zero, abs_of_nonneg hu,
    abs_of_nonneg (sub_nonneg.mpr huv), abs_of_nonneg (sub_nonneg.mpr hv)] at hinner hleft hright
  have houter : |f v - f u| ≤ |f u - f 0| + |f a - f v| := by
    calc
      _ ≤ |f v - f 0| + |f 0 - f u| := abs_sub_le _ _ _
      _ = _ := by rw [abs_sub_comm (f v) (f 0), abs_sub_comm (f 0) (f u), hperiod]; ring
  nlinarith

theorem closedLoop_range_le
    {f : ℝ → ℝ} {a u v : ℝ} {L : NNReal}
    (ha : 0 ≤ a) (hf : LipschitzOnWith L f (uIcc (0 : ℝ) a))
    (hperiod : f 0 = f a)
    (hu : u ∈ Icc (0 : ℝ) a) (hv : v ∈ Icc (0 : ℝ) a) :
    |f v - f u| ≤ (L : ℝ) * a / 2 := by
  rcases le_total u v with huv | hvu
  · exact closedLoop_range_le_ordered ha hf hperiod hu.1 huv hv.2
  · rw [abs_sub_comm]
    exact closedLoop_range_le_ordered ha hf hperiod hv.1 hvu hu.2

/-- Exact final arithmetic for the sharp coefficient. -/
theorem variance_range_polynomial_bound {D X : ℝ} (hD : 0 ≤ D) (hX : 0 ≤ X) :
    X * D ^ 2 / 4 - D ^ 3 / 3 ≤ X ^ 3 / 48 := by
  have hprod := mul_nonneg (sq_nonneg (X - 2 * D)) (by linarith : 0 ≤ X + 4 * D)
  nlinarith

theorem closedLoop_sub_const {f : ℝ → ℝ} {a : ℝ} {L : NNReal}
    (hf : LipschitzOnWith L f (uIcc (0 : ℝ) a)) (c : ℝ) :
    LipschitzOnWith L (fun t => f t - c) (uIcc (0 : ℝ) a) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have h := hf.dist_le_mul x hx y hy
  simp only [Real.dist_eq] at h ⊢
  rw [show f x - c - (f y - c) = f x - f y by ring]
  exact h

theorem integral_centered_square {f : ℝ → ℝ} {a : ℝ}
    (hf : ContinuousOn f (uIcc (0 : ℝ) a)) (c : ℝ) :
    (∫ t in (0 : ℝ)..a, (f t - c) ^ 2) =
      (∫ t in (0 : ℝ)..a, (f t) ^ 2) -
        2 * c * (∫ t in (0 : ℝ)..a, f t) + a * c ^ 2 := by
  have hi : IntervalIntegrable f volume 0 a := hf.intervalIntegrable
  have hi₂ : IntervalIntegrable (fun t => f t ^ 2) volume 0 a :=
    (hf.pow 2).intervalIntegrable
  have hlin := hi.const_mul (2 * c)
  calc
    _ = ∫ t in (0 : ℝ)..a, (f t ^ 2 - 2 * c * f t) + c ^ 2 := by
      apply intervalIntegral.integral_congr
      intro t _
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add (hi₂.sub hlin) intervalIntegrable_const,
        intervalIntegral.integral_sub hi₂ hlin, intervalIntegral.integral_const_mul]
      simp

/-- Sharp square-integral estimate after centering the attained range. -/
theorem closedLoop_centered_sq_integral
    {f : ℝ → ℝ} {a R u v : ℝ} {L : NNReal}
    (ha : 0 < a) (hL : 0 < (L : ℝ)) (hR : 0 ≤ R)
    (hf : LipschitzOnWith L f (uIcc (0 : ℝ) a)) (hperiod : f 0 = f a)
    (hbox : ∀ t ∈ Icc (0 : ℝ) a, |f t| ≤ R)
    (hu : u ∈ Icc (0 : ℝ) a) (hv : v ∈ Icc (0 : ℝ) a)
    (humin : f u = -R) (hvmax : f v = R) :
    (∫ t in (0 : ℝ)..a, f t ^ 2) ≤ (L : ℝ) ^ 2 * a ^ 3 / 48 := by
  have htwo := closedLoop_weight_lower ha.le hf hperiod hbox hu hv
  have hprim : variancePrimitive R R - variancePrimitive R (-R) = 4 * R ^ 3 / 3 := by
    unfold variancePrimitive
    ring
  rw [humin, hvmax, hprim, abs_of_nonneg (by positivity : 0 ≤ 4 * R ^ 3 / 3)] at htwo
  have hi₂ : IntervalIntegrable (fun t => f t ^ 2) volume 0 a :=
    (hf.continuousOn.pow 2).intervalIntegrable
  have hweight : (∫ t in (0 : ℝ)..a, varianceWeight R (f t)) =
      a * R ^ 2 - ∫ t in (0 : ℝ)..a, f t ^ 2 := by
    unfold varianceWeight
    rw [intervalIntegral.integral_sub intervalIntegrable_const hi₂]
    simp
  rw [hweight] at htwo
  have hfirst : (L : ℝ) * (∫ t in (0 : ℝ)..a, f t ^ 2) ≤
      ((L : ℝ) * a) * (2 * R) ^ 2 / 4 - (2 * R) ^ 3 / 3 := by nlinarith
  have hpoly := variance_range_polynomial_bound (D := 2 * R) (X := (L : ℝ) * a)
    (by positivity) (by positivity)
  apply (mul_le_mul_iff_right₀ hL).mp
  calc
    (L : ℝ) * (∫ t in (0 : ℝ)..a, f t ^ 2) ≤
        ((L : ℝ) * a) * (2 * R) ^ 2 / 4 - (2 * R) ^ 3 / 3 := hfirst
    _ ≤ ((L : ℝ) * a) ^ 3 / 48 := hpoly
    _ = (L : ℝ) * ((L : ℝ) ^ 2 * a ^ 3 / 48) := by ring

/-- The sharp zero-mean estimate for a positive Lipschitz bound. Extrema
exist by compactness and the complete two-arc argument is discharged above. -/
theorem closedLoop_zeroMean_sq_integral_of_pos
    {f : ℝ → ℝ} {a : ℝ} {L : NNReal}
    (ha : 0 < a) (hL : 0 < (L : ℝ))
    (hf : LipschitzOnWith L f (uIcc (0 : ℝ) a)) (hperiod : f 0 = f a)
    (hmean : (∫ t in (0 : ℝ)..a, f t) = 0) :
    (∫ t in (0 : ℝ)..a, f t ^ 2) ≤ (L : ℝ) ^ 2 * a ^ 3 / 48 := by
  have hc : ContinuousOn f (Icc (0 : ℝ) a) := by
    simpa only [uIcc_of_le ha.le] using hf.continuousOn
  have hne : (Icc (0 : ℝ) a).Nonempty := ⟨0, le_rfl, ha.le⟩
  obtain ⟨u, hu, hmin⟩ := isCompact_Icc.exists_isMinOn hne hc
  obtain ⟨v, hv, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hc
  let R := (f v - f u) / 2
  let c := (f v + f u) / 2
  let g := fun t => f t - c
  have hR : 0 ≤ R := by
    have h : f u ≤ f v := hmin hv
    dsimp [R]
    linarith
  have hg : LipschitzOnWith L g (uIcc (0 : ℝ) a) := closedLoop_sub_const hf c
  have hgp : g 0 = g a := by dsimp [g]; rw [hperiod]
  have hgbox : ∀ t ∈ Icc (0 : ℝ) a, |g t| ≤ R := by
    intro t ht
    have hlow : f u ≤ f t := hmin ht
    have hhigh : f t ≤ f v := hmax ht
    apply abs_le.mpr
    dsimp [g, c, R]
    constructor <;> linarith
  have hgu : g u = -R := by dsimp [g, c, R]; ring
  have hgv : g v = R := by dsimp [g, c, R]; ring
  have hcenter := closedLoop_centered_sq_integral ha hL hR hg hgp hgbox hu hv hgu hgv
  change (∫ t in (0 : ℝ)..a, (f t - c) ^ 2) ≤ _ at hcenter
  have hexpand := integral_centered_square hf.continuousOn c
  rw [hmean] at hexpand
  have hpos : 0 ≤ a * c ^ 2 := mul_nonneg ha.le (sq_nonneg c)
  linarith

/-- Sharp normalized variance bound when the Lipschitz constant is positive. -/
theorem closedLoop_variance_bound_of_pos
    {f : ℝ → ℝ} {a : ℝ} {L : NNReal}
    (ha : 0 < a) (hL : 0 < (L : ℝ))
    (hf : LipschitzOnWith L f (uIcc (0 : ℝ) a)) (hperiod : f 0 = f a) :
    (∫ t in (0 : ℝ)..a, f t ^ 2) / a -
      ((∫ t in (0 : ℝ)..a, f t) / a) ^ 2 ≤ (L : ℝ) ^ 2 * a ^ 2 / 48 := by
  let μ := (∫ t in (0 : ℝ)..a, f t) / a
  let g := fun t => f t - μ
  have hg : LipschitzOnWith L g (uIcc (0 : ℝ) a) := closedLoop_sub_const hf μ
  have hgp : g 0 = g a := by dsimp [g]; rw [hperiod]
  have hgm : (∫ t in (0 : ℝ)..a, g t) = 0 := by
    change (∫ t in (0 : ℝ)..a, f t - μ) = 0
    rw [intervalIntegral.integral_sub hf.continuousOn.intervalIntegrable intervalIntegrable_const]
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    dsimp [μ]
    field_simp
    ring
  have hsq := closedLoop_zeroMean_sq_integral_of_pos ha hL hg hgp hgm
  have hexpand := integral_centered_square hf.continuousOn μ
  have heq : (∫ t in (0 : ℝ)..a, g t ^ 2) / a =
      (∫ t in (0 : ℝ)..a, f t ^ 2) / a -
        ((∫ t in (0 : ℝ)..a, f t) / a) ^ 2 := by
    change (∫ t in (0 : ℝ)..a, (f t - μ) ^ 2) / a = _
    rw [hexpand]
    dsimp [μ]
    field_simp
    ring
  rw [← heq]
  apply (div_le_iff₀ ha).mpr
  convert hsq using 1
  ring

/-- Zero Lipschitz constant forces constancy, closing the degenerate case. -/
theorem closedLoop_variance_bound
    {f : ℝ → ℝ} {a : ℝ} {L : NNReal}
    (ha : 0 < a)
    (hf : LipschitzOnWith L f (uIcc (0 : ℝ) a)) (hperiod : f 0 = f a) :
    (∫ t in (0 : ℝ)..a, f t ^ 2) / a -
      ((∫ t in (0 : ℝ)..a, f t) / a) ^ 2 ≤ (L : ℝ) ^ 2 * a ^ 2 / 48 := by
  by_cases hL : (L : ℝ) = 0
  · have hconst : ∀ t ∈ uIcc (0 : ℝ) a, f t = f 0 := by
      intro t ht
      have h := hf.dist_le_mul t ht 0 left_mem_uIcc
      rw [hL, zero_mul, dist_le_zero] at h
      exact h
    have hi : (∫ t in (0 : ℝ)..a, f t) = a * f 0 := by
      calc
        _ = ∫ _t in (0 : ℝ)..a, f 0 := by
          apply intervalIntegral.integral_congr
          exact hconst
        _ = _ := by simp
    have hi₂ : (∫ t in (0 : ℝ)..a, f t ^ 2) = a * f 0 ^ 2 := by
      calc
        _ = ∫ _t in (0 : ℝ)..a, f 0 ^ 2 := by
          apply intervalIntegral.integral_congr
          intro t ht
          change f t ^ 2 = f 0 ^ 2
          rw [hconst t ht]
        _ = _ := by simp
    rw [hi, hi₂, hL]
    simp [ha.ne']
  · exact closedLoop_variance_bound_of_pos ha
      (lt_of_le_of_ne (NNReal.coe_nonneg L) (Ne.symm hL)) hf hperiod

/-- The exact alias constant used by the phase Gram constraints. -/
theorem closedLoop_alias_variance
    {f : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hf : LipschitzOnWith 2 f (uIcc (0 : ℝ) a)) (hperiod : f 0 = f a)
    (hmean : (∫ t in (0 : ℝ)..a, f t) = 0) :
    (∫ t in (0 : ℝ)..a, f t ^ 2) / a ≤ a ^ 2 / 12 := by
  have h := closedLoop_variance_bound ha hf hperiod
  rw [hmean] at h
  norm_num at h ⊢
  nlinarith

/-- A periodic function satisfies the closed-loop boundary condition. -/
theorem periodic_variance_bound
    {f : ℝ → ℝ} {a : ℝ} {L : NNReal} (ha : 0 < a)
    (hf : LipschitzOnWith L f (uIcc (0 : ℝ) a))
    (hperiod : Function.Periodic f a) :
    (∫ t in (0 : ℝ)..a, f t ^ 2) / a -
      ((∫ t in (0 : ℝ)..a, f t) / a) ^ 2 ≤ (L : ℝ) ^ 2 * a ^ 2 / 48 := by
  apply closedLoop_variance_bound ha hf
  simpa only [zero_add] using (hperiod 0).symm

/-- The alias estimate on the actual phase interval `[-a,0]`. -/
theorem closedLoop_alias_variance_shifted
    {f : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hf : LipschitzWith 2 f) (hperiod : f (-a) = f 0)
    (hmean : (∫ t in -a..(0 : ℝ), f t) = 0) :
    (∫ t in -a..(0 : ℝ), f t ^ 2) / a ≤ a ^ 2 / 12 := by
  let g : ℝ → ℝ := fun t => f (t - a)
  have hg : LipschitzOnWith 2 g (uIcc (0 : ℝ) a) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x _ y _
    have h := hf.dist_le_mul (x - a) (y - a)
    simpa only [g, Real.dist_eq, sub_sub_sub_cancel_right] using h
  have hgp : g 0 = g a := by simpa [g] using hperiod
  have hgm : (∫ t in (0 : ℝ)..a, g t) = 0 := by
    dsimp [g]
    rw [intervalIntegral.integral_comp_sub_right]
    simpa using hmean
  have h := closedLoop_alias_variance ha hg hgp hgm
  have hshift : (∫ t in (0 : ℝ)..a, (f (t - a)) ^ 2) =
      ∫ t in -a..(0 : ℝ), f t ^ 2 := by
    convert! intervalIntegral.integral_comp_sub_right
      (fun x : ℝ => f x ^ 2) (a := 0) (b := a) a using 1
    simp
  convert! h using 1
  dsimp [g]
  rw [hshift]

end

end

end ErdosOverlap
