/-
Copyright (c) 2026. Released under BSD-3-Clause license.

An exact, nonnegative remainder for the continuous profile dual.
The conclusions concern distance from a specified certificate return;
they make no claim that this return equals the unknown optimal constant.
-/
module

public import ErdosOverlap.ContinuousDual

open MeasureTheory Set

namespace ErdosOverlap

public section

noncomputable section

/-- The scalar gap in the explicitly computed profile conjugate. -/
@[expose] def profileGap (b c L U lam z : ℝ) : ℝ :=
  profileCost b c L z - lam * z - profileConjugate b c L U lam

/-- The loss in the derivative estimate `v * d' ≤ |v|`. -/
@[expose] def flowDefect (v dp : ℝ) : ℝ := |v| - v * dp

theorem profileGap_nonneg {b c L U lam z : ℝ}
    (hb : 0 ≤ b) (hbc : b ≤ c) (hL : 0 ≤ L) (hU : 0 ≤ U)
    (hz : |z| ≤ U) : 0 ≤ profileGap b c L U lam z := by
  dsimp [profileGap]
  exact sub_nonneg.mpr (profileConjugate_le_cost_sub_linear hb hbc hL hU hz)

theorem flowDefect_nonneg {v dp : ℝ} (hdp : |dp| ≤ 1) :
    0 ≤ flowDefect v dp := by
  exact sub_nonneg.mpr (mul_le_abs_of_abs_le_one hdp)

/-- On a positive test-function region, the derivative defect is the
weighted endpoint discrepancy from the ordered pair `(1,0)`. -/
theorem flowDefect_endpoint_positive {v a b : ℝ} (hv : 0 ≤ v) :
    flowDefect v (a - b) = v * ((1 - a) + b) := by
  rw [flowDefect, abs_of_nonneg hv]
  ring

/-- On a negative test-function region, the prescribed endpoint pair is `(0,1)`. -/
theorem flowDefect_endpoint_negative {v a b : ℝ} (hv : v ≤ 0) :
    flowDefect v (a - b) = (-v) * (a + (1 - b)) := by
  rw [flowDefect, abs_of_nonpos hv]
  ring

/-- A positive lower bound for the witness weight turns the weighted
endpoint defect into an ordinary endpoint-discrepancy estimate. -/
theorem positive_endpoint_discrepancy_bound {v a b ν ε : ℝ}
    (hν : 0 < ν) (hv : ν ≤ v) (ha : a ≤ 1) (hb : 0 ≤ b)
    (hdefect : flowDefect v (a - b) ≤ ε) :
    (1 - a) + b ≤ ε / ν := by
  have hv0 : 0 ≤ v := le_trans (le_of_lt hν) hv
  rw [flowDefect_endpoint_positive hv0] at hdefect
  have hdist : 0 ≤ (1 - a) + b := by linarith
  apply (le_div_iff₀ hν).mpr
  nlinarith

theorem negative_endpoint_discrepancy_bound {v a b ν ε : ℝ}
    (hν : 0 < ν) (hv : ν ≤ -v) (ha : 0 ≤ a) (hb : b ≤ 1)
    (hdefect : flowDefect v (a - b) ≤ ε) :
    a + (1 - b) ≤ ε / ν := by
  have hv0 : v ≤ 0 := by linarith
  rw [flowDefect_endpoint_negative hv0] at hdefect
  have hdist : 0 ≤ a + (1 - b) := by linarith
  apply (le_div_iff₀ hν).mpr
  nlinarith

/-- The two stability integrands are integrable under exactly the analytic
hypotheses used for the dual. -/
theorem intervalIntegrable_profileGap {b c L U d v : ℝ → ℝ} (τ : ℝ)
    (hd : AbsolutelyContinuousOnInterval d 0 1)
    (hv : AbsolutelyContinuousOnInterval v 0 1)
    (hcost : IntervalIntegrable
      (fun x => profileCost (b x) (c x) (L x) (d x)) volume 0 1)
    (hconj : IntervalIntegrable
      (fun x => profileConjugate (b x) (c x) (L x) (U x)
        (dualSlope τ v x)) volume 0 1) :
    IntervalIntegrable
      (fun x => profileGap (b x) (c x) (L x) (U x) (dualSlope τ v x) (d x))
      volume 0 1 := by
  exact (hcost.sub (intervalIntegrable_dualSlope_mul τ hd hv)).sub hconj

theorem intervalIntegrable_flowDefect {d v : ℝ → ℝ}
    (hd : AbsolutelyContinuousOnInterval d 0 1)
    (hv : AbsolutelyContinuousOnInterval v 0 1) :
    IntervalIntegrable (fun x => flowDefect (v x) (deriv d x)) volume 0 1 := by
  exact hv.continuousOn.abs.intervalIntegrable.sub
    (hd.intervalIntegrable_deriv.continuousOn_mul hv.continuousOn)

/-- The exact remainder identity. Integration by parts is proved by mathlib
for actual absolutely continuous functions, not supplied as a hypothesis. -/
theorem interval_profile_remainder_identity {b c L U d v : ℝ → ℝ} (τ : ℝ)
    (hd : AbsolutelyContinuousOnInterval d 0 1)
    (hv : AbsolutelyContinuousOnInterval v 0 1)
    (hd0 : d 0 = 0) (hv1 : v 1 = 0)
    (hcost : IntervalIntegrable
      (fun x => profileCost (b x) (c x) (L x) (d x)) volume 0 1)
    (hconj : IntervalIntegrable
      (fun x => profileConjugate (b x) (c x) (L x) (U x)
        (dualSlope τ v x)) volume 0 1) :
    (∫ x in (0 : ℝ)..1,
        profileGap (b x) (c x) (L x) (U x) (dualSlope τ v x) (d x)) +
      (∫ x in (0 : ℝ)..1, flowDefect (v x) (deriv d x)) =
      (∫ x in (0 : ℝ)..1, profileCost (b x) (c x) (L x) (d x)) -
        τ * profileMean d + (∫ x in (0 : ℝ)..1, |v x|) -
        (∫ x in (0 : ℝ)..1,
          profileConjugate (b x) (c x) (L x) (U x) (dualSlope τ v x)) := by
  have hlin := intervalIntegrable_dualSlope_mul τ hd hv
  have hprod : IntervalIntegrable (fun x => v x * deriv d x) volume 0 1 :=
    hd.intervalIntegrable_deriv.continuousOn_mul hv.continuousOn
  have habs : IntervalIntegrable (fun x => |v x|) volume 0 1 :=
    hv.continuousOn.abs.intervalIntegrable
  simp only [profileGap, flowDefect,
    intervalIntegral.integral_sub (hcost.sub hlin) hconj,
    intervalIntegral.integral_sub hcost hlin,
    intervalIntegral.integral_sub habs hprod]
  rw [integral_dualSlope_mul τ hd hv hd0 hv1]
  ring

/-- Both components of the remainder are nonnegative. -/
theorem interval_profile_remainders_nonneg {b c L U d v : ℝ → ℝ} (τ : ℝ)
    (hd : LipschitzOnWith 1 d (uIcc (0 : ℝ) 1))
    (hv : AbsolutelyContinuousOnInterval v 0 1)
    (hb : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ b x)
    (hbc : ∀ x ∈ Icc (0 : ℝ) 1, b x ≤ c x)
    (hL : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ L x)
    (hU : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ U x)
    (hbox : ∀ x ∈ Icc (0 : ℝ) 1, |d x| ≤ U x) :
    0 ≤ (∫ x in (0 : ℝ)..1,
        profileGap (b x) (c x) (L x) (U x) (dualSlope τ v x) (d x)) ∧
      0 ≤ (∫ x in (0 : ℝ)..1, flowDefect (v x) (deriv d x)) := by
  constructor
  · apply intervalIntegral.integral_nonneg zero_le_one
    intro x hx
    exact profileGap_nonneg (hb x hx) (hbc x hx) (hL x hx) (hU x hx) (hbox x hx)
  · have hflow := intervalIntegrable_flowDefect hd.absolutelyContinuousOnInterval hv
    have hzero : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 0 1 :=
      intervalIntegrable_const
    have hle := intervalIntegral.integral_mono_on_of_le_Ioo
      zero_le_one hzero hflow (fun x hx => flowDefect_nonneg (abs_deriv_le_one_on_Ioo hd hx))
    simpa only [intervalIntegral.integral_zero] using hle

/-- The exact remainder is bounded by the slack in a physical kernel budget.
The scalar `J` is any proved lower bound for the conjugate integral; outward
numerical errors are therefore already included on the right-hand side. -/
theorem interval_profile_stability {b c L U d v : ℝ → ℝ} (τ : ℝ)
    {ℓ M D J : ℝ}
    (hd : AbsolutelyContinuousOnInterval d 0 1)
    (hv : AbsolutelyContinuousOnInterval v 0 1)
    (hd0 : d 0 = 0) (hv1 : v 1 = 0)
    (hcost : IntervalIntegrable
      (fun x => profileCost (b x) (c x) (L x) (d x)) volume 0 1)
    (hconj : IntervalIntegrable
      (fun x => profileConjugate (b x) (c x) (L x) (U x)
        (dualSlope τ v x)) volume 0 1)
    (hbudget : ℓ + (∫ x in (0 : ℝ)..1,
      profileCost (b x) (c x) (L x) (d x)) ≤ M * D)
    (hJ : J ≤ ∫ x in (0 : ℝ)..1,
      profileConjugate (b x) (c x) (L x) (U x) (dualSlope τ v x)) :
    (∫ x in (0 : ℝ)..1,
        profileGap (b x) (c x) (L x) (U x) (dualSlope τ v x) (d x)) +
      (∫ x in (0 : ℝ)..1, flowDefect (v x) (deriv d x)) ≤
      M * D - (ℓ + τ * profileMean d - (∫ x in (0 : ℝ)..1, |v x|) + J) := by
  rw [interval_profile_remainder_identity τ hd hv hd0 hv1 hcost hconj]
  linarith

/-- If the physical peak is within `ε` of an explicit dual return, the
sum of both structural defects is at most `D * ε`. This is conditional
closeness to the certificate return, not to an asserted optimizer. -/
theorem interval_profile_stability_of_return {b c L U d v : ℝ → ℝ} (τ : ℝ)
    {ℓ M D J β ε : ℝ}
    (hd : AbsolutelyContinuousOnInterval d 0 1)
    (hv : AbsolutelyContinuousOnInterval v 0 1)
    (hd0 : d 0 = 0) (hv1 : v 1 = 0)
    (hcost : IntervalIntegrable
      (fun x => profileCost (b x) (c x) (L x) (d x)) volume 0 1)
    (hconj : IntervalIntegrable
      (fun x => profileConjugate (b x) (c x) (L x) (U x)
        (dualSlope τ v x)) volume 0 1)
    (hbudget : ℓ + (∫ x in (0 : ℝ)..1,
      profileCost (b x) (c x) (L x) (d x)) ≤ M * D)
    (hJ : J ≤ ∫ x in (0 : ℝ)..1,
      profileConjugate (b x) (c x) (L x) (U x) (dualSlope τ v x))
    (hD : 0 ≤ D)
    (hreturn : β * D ≤
      ℓ + τ * profileMean d - (∫ x in (0 : ℝ)..1, |v x|) + J)
    (hpeak : M ≤ β + ε) :
    (∫ x in (0 : ℝ)..1,
        profileGap (b x) (c x) (L x) (U x) (dualSlope τ v x) (d x)) +
      (∫ x in (0 : ℝ)..1, flowDefect (v x) (deriv d x)) ≤ D * ε := by
  have hstab := interval_profile_stability τ hd hv hd0 hv1 hcost hconj hbudget hJ
  have hMD := mul_le_mul_of_nonneg_right hpeak hD
  nlinarith

end

end

end ErdosOverlap
