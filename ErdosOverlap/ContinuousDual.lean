/-
Copyright (c) 2026. Released under BSD-3-Clause license.

The continuous odd-profile dual on the actual Lebesgue interval [0,1].
No numerical certificate, Fourier expectation, or integration-by-parts
identity is postulated as an axiom in this file.
-/
module

public import ErdosOverlap.Pointwise
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.Calculus.Deriv.Basic

open MeasureTheory Set

namespace ErdosOverlap

public section

noncomputable section

/-- The derivative coefficient in the continuous dual. -/
@[expose] def dualSlope (τ : ℝ) (v : ℝ → ℝ) (x : ℝ) : ℝ :=
  2 * τ + deriv v x

/-- The first overlap moment expressed through the folded odd profile. -/
@[expose] def profileMean (d : ℝ → ℝ) : ℝ :=
  2 * ∫ x in (0 : ℝ)..1, d x

/-- The elementary estimate responsible for the Lipschitz dual cost. -/
theorem mul_le_abs_of_abs_le_one {r s : ℝ} (hs : |s| ≤ 1) :
    r * s ≤ |r| := by
  calc
    r * s ≤ |r * s| := le_abs_self _
    _ = |r| * |s| := abs_mul _ _
    _ ≤ |r| * 1 := mul_le_mul_of_nonneg_left hs (abs_nonneg _)
    _ = |r| := mul_one _

/-- The product appearing in the dual is genuinely interval integrable
for absolutely continuous test functions and profiles. -/
theorem intervalIntegrable_dualSlope_mul {d v : ℝ → ℝ} (τ : ℝ)
    (hd : AbsolutelyContinuousOnInterval d 0 1)
    (hv : AbsolutelyContinuousOnInterval v 0 1) :
    IntervalIntegrable (fun x => dualSlope τ v x * d x) volume 0 1 := by
  have h₁ : IntervalIntegrable (fun x => (2 * τ) * d x) volume 0 1 :=
    hd.continuousOn.intervalIntegrable.const_mul (2 * τ)
  have h₂ : IntervalIntegrable (fun x => deriv v x * d x) volume 0 1 :=
    hv.intervalIntegrable_deriv.mul_continuousOn hd.continuousOn
  simpa only [dualSlope, add_mul] using h₁.add h₂

/-- Actual integration by parts on `[0,1]`, valid for absolutely continuous
functions and therefore not restricted to globally differentiable test data. -/
theorem integral_dualSlope_mul {d v : ℝ → ℝ} (τ : ℝ)
    (hd : AbsolutelyContinuousOnInterval d 0 1)
    (hv : AbsolutelyContinuousOnInterval v 0 1)
    (hd0 : d 0 = 0) (hv1 : v 1 = 0) :
    (∫ x in (0 : ℝ)..1, dualSlope τ v x * d x) =
      τ * profileMean d - ∫ x in (0 : ℝ)..1, v x * deriv d x := by
  have h₁ : IntervalIntegrable (fun x => (2 * τ) * d x) volume 0 1 :=
    hd.continuousOn.intervalIntegrable.const_mul (2 * τ)
  have h₂ : IntervalIntegrable (fun x => deriv v x * d x) volume 0 1 :=
    hv.intervalIntegrable_deriv.mul_continuousOn hd.continuousOn
  have hparts := hv.integral_mul_deriv_eq_deriv_mul hd
  simp only [hv1, hd0, zero_mul, mul_zero, sub_self, zero_sub] at hparts
  calc
    (∫ x in (0 : ℝ)..1, dualSlope τ v x * d x) =
        ∫ x in (0 : ℝ)..1, (2 * τ) * d x + deriv v x * d x := by
      apply intervalIntegral.integral_congr
      intro x hx
      simp only [dualSlope, add_mul]
    _ = (∫ x in (0 : ℝ)..1, (2 * τ) * d x) +
        ∫ x in (0 : ℝ)..1, deriv v x * d x :=
      intervalIntegral.integral_add h₁ h₂
    _ = τ * profileMean d - ∫ x in (0 : ℝ)..1, v x * deriv d x := by
      rw [intervalIntegral.integral_const_mul]
      dsimp [profileMean]
      nlinarith [hparts]

/-- A 1-Lipschitz function has derivative of magnitude at most one at
every interior point, with mathlib's total derivative convention. -/
theorem abs_deriv_le_one_on_Ioo {d : ℝ → ℝ}
    (hd : LipschitzOnWith 1 d (uIcc (0 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : |deriv d x| ≤ 1 := by
  have hmem : uIcc (0 : ℝ) 1 ∈ nhds x := by
    rw [uIcc_of_le zero_le_one]
    exact Icc_mem_nhds hx.1 hx.2
  simpa only [Real.norm_eq_abs, NNReal.coe_one] using
    norm_deriv_le_of_lipschitzOn hmem hd

/-- An actual interval-integral lower bound from a scalar conjugate and
an absolutely continuous test function. The function `ψ` may be any
integrable pointwise lower conjugate; the concrete profile version follows. -/
theorem interval_dual_of_pointwise {d v F ψ : ℝ → ℝ} (τ : ℝ)
    (hd : LipschitzOnWith 1 d (uIcc (0 : ℝ) 1))
    (hv : AbsolutelyContinuousOnInterval v 0 1)
    (hd0 : d 0 = 0) (hv1 : v 1 = 0)
    (hF : IntervalIntegrable F volume 0 1)
    (hψ : IntervalIntegrable ψ volume 0 1)
    (hpoint : ∀ x ∈ Icc (0 : ℝ) 1, ψ x ≤ F x - dualSlope τ v x * d x) :
    τ * profileMean d - (∫ x in (0 : ℝ)..1, |v x|) +
        (∫ x in (0 : ℝ)..1, ψ x) ≤ ∫ x in (0 : ℝ)..1, F x := by
  have hdac := hd.absolutelyContinuousOnInterval
  have hlin := intervalIntegrable_dualSlope_mul τ hdac hv
  have hprod : IntervalIntegrable (fun x => v x * deriv d x) volume 0 1 :=
    hdac.intervalIntegrable_deriv.continuousOn_mul hv.continuousOn
  have habs : IntervalIntegrable (fun x => |v x|) volume 0 1 :=
    hv.continuousOn.abs.intervalIntegrable
  have hprod_le : (∫ x in (0 : ℝ)..1, v x * deriv d x) ≤
      ∫ x in (0 : ℝ)..1, |v x| := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one hprod habs
    intro x hx
    exact mul_le_abs_of_abs_le_one (abs_deriv_le_one_on_Ioo hd hx)
  have hconj := intervalIntegral.integral_mono_on zero_le_one hψ (hF.sub hlin) hpoint
  rw [intervalIntegral.integral_sub hF hlin] at hconj
  have hparts := integral_dualSlope_mul τ hdac hv hd0 hv1
  linarith

/-- Universal continuous profile-dual inequality on the Lebesgue interval.
All analytic regularity and integrability assumptions are explicit. -/
theorem interval_profile_dual {b c L U d v : ℝ → ℝ} (τ : ℝ)
    (hd : LipschitzOnWith 1 d (uIcc (0 : ℝ) 1))
    (hv : AbsolutelyContinuousOnInterval v 0 1)
    (hd0 : d 0 = 0) (hv1 : v 1 = 0)
    (hb : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ b x)
    (hbc : ∀ x ∈ Icc (0 : ℝ) 1, b x ≤ c x)
    (hL : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ L x)
    (hU : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ U x)
    (hbox : ∀ x ∈ Icc (0 : ℝ) 1, |d x| ≤ U x)
    (hcost : IntervalIntegrable (fun x => profileCost (b x) (c x) (L x) (d x)) volume 0 1)
    (hconj : IntervalIntegrable
      (fun x => profileConjugate (b x) (c x) (L x) (U x) (dualSlope τ v x)) volume 0 1) :
    τ * profileMean d - (∫ x in (0 : ℝ)..1, |v x|) +
      (∫ x in (0 : ℝ)..1,
        profileConjugate (b x) (c x) (L x) (U x) (dualSlope τ v x)) ≤
      ∫ x in (0 : ℝ)..1, profileCost (b x) (c x) (L x) (d x) := by
  apply interval_dual_of_pointwise τ hd hv hd0 hv1 hcost hconj
  intro x hx
  exact profileConjugate_le_cost_sub_linear (hb x hx) (hbc x hx)
    (hL x hx) (hU x hx) (hbox x hx)

end

end

end ErdosOverlap
