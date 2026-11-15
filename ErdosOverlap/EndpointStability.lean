/-
Copyright (c) 2026. Released under the BSD-3-Clause license.

Physical endpoint interpretation of the continuous dual remainder for an
arbitrary measurable relaxed partition. The a.e. derivative identity is
proved using the Lebesgue differentiation theorem.
-/
module

public import ErdosOverlap.Overlap
public import ErdosOverlap.Stability
public import ErdosOverlap.KernelDual
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

open MeasureTheory Set
open scoped Interval

namespace ErdosOverlap

public section

noncomputable section

/-- The ordinary L1 distance of an endpoint pair from the coloring prescribed
by the sign of the dual witness. The convention at zero is immaterial after
multiplication by the witness weight. -/
@[expose] def endpointDiscrepancy (v a b : ℝ) : ℝ :=
  if 0 ≤ v then |1 - a| + |b| else |a| + |1 - b|

theorem endpointDiscrepancy_nonneg (v a b : ℝ) :
    0 ≤ endpointDiscrepancy v a b := by
  unfold endpointDiscrepancy
  split_ifs <;> positivity

/-- The scalar flow defect is exactly a weighted L1 distance, including the
degenerate case where the witness vanishes. -/
theorem flowDefect_eq_weighted_endpointDiscrepancy {v a b : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    flowDefect v (a - b) = |v| * endpointDiscrepancy v a b := by
  by_cases hv : 0 ≤ v
  · rw [flowDefect_endpoint_positive hv, endpointDiscrepancy, ite_eq_left hv,
      abs_of_nonneg hv, abs_of_nonneg (sub_nonneg.mpr ha1), abs_of_nonneg hb0]
  · rw [flowDefect_endpoint_negative (le_of_not_ge hv), endpointDiscrepancy, ite_eq_right hv,
      abs_of_nonpos (le_of_not_ge hv), abs_of_nonneg ha0,
      abs_of_nonneg (sub_nonneg.mpr hb1)]

/-- For an arbitrary measurable relaxed partition, the physical profile has
the claimed endpoint-difference derivative almost everywhere on `[0,1]`. -/
theorem overlapProfile_ae_hasDerivAt {h : ℝ → ℝ} (hh : Admissible h) :
    ∀ᵐ x ∂volume, x ∈ Icc (0 : ℝ) 1 →
      HasDerivAt (overlapProfile h) (profileSlope h x) x := by
  let : NormedSpace ℝ ℝ :=
    { toModule := (inferInstance : Module ℝ ℝ)
      norm_smul_le := fun r x => by
        simpa only [smul_eq_mul] using norm_mul_le r x }
  have hi := profileSlope_intervalIntegrable hh (a := 0) (b := 1)
    (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [hi.ae_hasDerivAt_integral] with x hx
  intro hxi
  have hxu : x ∈ uIcc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le zero_le_one] using hxi
  have hder := hx hxu 0 (by simp)
  unfold overlapProfile
  convert! hder using 1

theorem overlapProfile_ae_deriv {h : ℝ → ℝ} (hh : Admissible h) :
    ∀ᵐ x ∂volume.restrict (Icc (0 : ℝ) 1),
      deriv (overlapProfile h) x = profileSlope h x := by
  apply (ae_restrict_iff' measurableSet_Icc).mpr
  filter_upwards [overlapProfile_ae_hasDerivAt hh] with x hx
  intro hxi
  exact (hx hxi).deriv

/-- Pointwise a.e. equality between the analytic remainder and the actual
endpoint coloring discrepancy of the measurable partition. -/
theorem overlapProfile_ae_flowDefect {h v : ℝ → ℝ} (hh : Admissible h) :
    ∀ᵐ x ∂volume, x ∈ Icc (0 : ℝ) 1 →
      flowDefect (v x) (deriv (overlapProfile h) x) =
        |v x| * endpointDiscrepancy (v x) (h x) (h (2 - x)) := by
  filter_upwards [overlapProfile_ae_hasDerivAt hh] with x hx
  intro hxi
  have hxl : x ∈ Icc (0 : ℝ) 2 := ⟨hxi.1, by linarith [hxi.2]⟩
  have hxr : 2 - x ∈ Icc (0 : ℝ) 2 :=
    ⟨by linarith [hxi.2], by linarith [hxi.1]⟩
  rw [(hx hxi).deriv]
  exact flowDefect_eq_weighted_endpointDiscrepancy
    (hh.nonneg x hxl) (hh.le_one x hxl)
    (hh.nonneg (2 - x) hxr) (hh.le_one (2 - x) hxr)

/-- The exact integrated physical endpoint-error identity. -/
theorem integral_flowDefect_eq_weighted_endpointDiscrepancy
    {h v : ℝ → ℝ} (hh : Admissible h) :
    (∫ x in (0 : ℝ)..1, flowDefect (v x) (deriv (overlapProfile h) x)) =
      ∫ x in (0 : ℝ)..1,
        |v x| * endpointDiscrepancy (v x) (h x) (h (2 - x)) := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [overlapProfile_ae_flowDefect (v := v) hh] with x hx
  intro hxi
  rw [uIoc_of_le zero_le_one] at hxi
  exact hx ⟨le_of_lt hxi.1, hxi.2⟩

/-- Absolute continuity of the witness is enough to make the weighted
physical endpoint discrepancy integrable. No step-function assumption on
the partition is made. -/
theorem intervalIntegrable_weighted_endpointDiscrepancy
    {h v : ℝ → ℝ} (hh : Admissible h)
    (hv : AbsolutelyContinuousOnInterval v 0 1) :
    IntervalIntegrable (fun x =>
      |v x| * endpointDiscrepancy (v x) (h x) (h (2 - x))) volume 0 1 := by
  have hflow := intervalIntegrable_flowDefect
    (overlapProfile_lipschitz hh).absolutelyContinuousOnInterval hv
  apply hflow.congr_ae
  apply (ae_restrict_iff' measurableSet_uIoc).mpr
  filter_upwards [overlapProfile_ae_flowDefect (v := v) hh] with x hx
  intro hxi
  rw [uIoc_of_le zero_le_one] at hxi
  exact hx ⟨le_of_lt hxi.1, hxi.2⟩

/-- The complete physical remainder identity: both the profile mismatch and
the endpoint coloring error are actual integrals of the measurable partition. -/
theorem physical_profile_remainder_identity
    {h b c L U v : ℝ → ℝ} (τ : ℝ) (hh : Admissible h)
    (hv : AbsolutelyContinuousOnInterval v 0 1) (hv1 : v 1 = 0)
    (hcost : IntervalIntegrable
      (fun x => profileCost (b x) (c x) (L x) (overlapProfile h x)) volume 0 1)
    (hconj : IntervalIntegrable
      (fun x => profileConjugate (b x) (c x) (L x) (U x)
        (dualSlope τ v x)) volume 0 1) :
    (∫ x in (0 : ℝ)..1,
        profileGap (b x) (c x) (L x) (U x) (dualSlope τ v x) (overlapProfile h x)) +
      (∫ x in (0 : ℝ)..1,
        |v x| * endpointDiscrepancy (v x) (h x) (h (2 - x))) =
      (∫ x in (0 : ℝ)..1,
        profileCost (b x) (c x) (L x) (overlapProfile h x)) -
        τ * profileMean (overlapProfile h) + (∫ x in (0 : ℝ)..1, |v x|) -
        (∫ x in (0 : ℝ)..1,
          profileConjugate (b x) (c x) (L x) (U x) (dualSlope τ v x)) := by
  have hid := interval_profile_remainder_identity τ
    (overlapProfile_lipschitz hh).absolutelyContinuousOnInterval hv
    (overlapProfile_zero h) hv1 hcost hconj
  rw [integral_flowDefect_eq_weighted_endpointDiscrepancy hh] at hid
  exact hid

/-- Conditional structural stability near a stated certificate return.
The hypotheses identify the precise physical kernel budget and numerical
integral enclosure that a certificate must establish. The conclusion includes
nonnegativity of both defects, so each is separately bounded by `D * ε`. -/
theorem physical_profile_stability_of_return
    {h b c L U v : ℝ → ℝ} (τ : ℝ) (hh : Admissible h)
    {ℓ M D J β ε : ℝ}
    (hv : AbsolutelyContinuousOnInterval v 0 1) (hv1 : v 1 = 0)
    (hb : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ b x)
    (hbc : ∀ x ∈ Icc (0 : ℝ) 1, b x ≤ c x)
    (hL : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ L x)
    (hU : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ U x)
    (hbox : ∀ x ∈ Icc (0 : ℝ) 1, |overlapProfile h x| ≤ U x)
    (hcost : IntervalIntegrable
      (fun x => profileCost (b x) (c x) (L x) (overlapProfile h x)) volume 0 1)
    (hconj : IntervalIntegrable
      (fun x => profileConjugate (b x) (c x) (L x) (U x)
        (dualSlope τ v x)) volume 0 1)
    (hbudget : ℓ + (∫ x in (0 : ℝ)..1,
      profileCost (b x) (c x) (L x) (overlapProfile h x)) ≤ M * D)
    (hJ : J ≤ ∫ x in (0 : ℝ)..1,
      profileConjugate (b x) (c x) (L x) (U x) (dualSlope τ v x))
    (hD : 0 ≤ D)
    (hreturn : β * D ≤ ℓ + τ * profileMean (overlapProfile h) -
      (∫ x in (0 : ℝ)..1, |v x|) + J)
    (hpeak : M ≤ β + ε) :
    0 ≤ (∫ x in (0 : ℝ)..1,
        profileGap (b x) (c x) (L x) (U x) (dualSlope τ v x) (overlapProfile h x)) ∧
      0 ≤ (∫ x in (0 : ℝ)..1,
        |v x| * endpointDiscrepancy (v x) (h x) (h (2 - x))) ∧
      (∫ x in (0 : ℝ)..1,
        profileGap (b x) (c x) (L x) (U x) (dualSlope τ v x) (overlapProfile h x)) +
      (∫ x in (0 : ℝ)..1,
        |v x| * endpointDiscrepancy (v x) (h x) (h (2 - x))) ≤ D * ε := by
  have hnonneg := interval_profile_remainders_nonneg τ
    (overlapProfile_lipschitz hh) hv hb hbc hL hU hbox
  have hbound := interval_profile_stability_of_return τ
    (overlapProfile_lipschitz hh).absolutelyContinuousOnInterval hv
    (overlapProfile_zero h) hv1 hcost hconj hbudget hJ hD hreturn hpeak
  rw [integral_flowDefect_eq_weighted_endpointDiscrepancy hh] at hnonneg hbound
  exact ⟨hnonneg.1, hnonneg.2, hbound⟩

/-- The concrete profile-conjugacy gap of an actual kernel witness. -/
@[expose] def kernelGap (h Q : ℝ → ℝ) (a H τ : ℝ) (v : ℝ → ℝ) (t : ℝ) : ℝ :=
  profileGap (max (Q (2 - t)) 0) (|Q t| + |Q (2 - t)|)
    (max (2 * a - t) 0) (min t H) (dualSlope τ v t) (overlapProfile h t)

/-- The structural stability theorem with the physical quartet budget
derived from the actual overlaps. Only the kernel expectation and conjugate
integral enclosure remain certificate-specific hypotheses. -/
theorem kernel_endpoint_stability_of_return
    {h Q v : ℝ → ℝ} {a M H ell τ J β ε : ℝ}
    (hh : Admissible h) (hcap : OverlapCap h M)
    (haM : a ≤ M) (hMH : M ≤ H)
    (hv : AbsolutelyContinuousOnInterval v 0 1) (hv1 : v 1 = 0)
    (hquartet : IntervalIntegrable (quartetIntegrand h Q) volume 0 1)
    (hcost : IntervalIntegrable (kernelCost h Q a) volume 0 1)
    (hpositive : IntervalIntegrable
      (fun t => max (Q t) 0 + max (Q (2 - t)) 0) volume 0 1)
    (hconj : IntervalIntegrable (kernelConjugate Q a H τ v) volume 0 1)
    (hell : ell ≤ quartetFunctional h Q)
    (hJ : J ≤ ∫ t in (0 : ℝ)..1, kernelConjugate Q a H τ v t)
    (hreturn : β * kernelDenominator Q ≤ ell + τ * profileMean (overlapProfile h) -
      (∫ t in (0 : ℝ)..1, |v t|) + J)
    (hpeak : M ≤ β + ε) :
    0 ≤ (∫ t in (0 : ℝ)..1, kernelGap h Q a H τ v t) ∧
      0 ≤ (∫ t in (0 : ℝ)..1,
        |v t| * endpointDiscrepancy (v t) (h t) (h (2 - t))) ∧
      (∫ t in (0 : ℝ)..1, kernelGap h Q a H τ v t) +
      (∫ t in (0 : ℝ)..1,
        |v t| * endpointDiscrepancy (v t) (h t) (h (2 - t))) ≤
          kernelDenominator Q * ε := by
  have hH : 0 ≤ H := (hcap.nonneg hh).trans hMH
  have hbudget := quartet_functional_add_cost_le hh hcap haM hquartet hcost hpositive
  have hbudget' : ell + (∫ t in (0 : ℝ)..1, kernelCost h Q a t) ≤
      M * kernelDenominator Q := by linarith
  exact physical_profile_stability_of_return τ hh hv hv1
    (fun _ _ => le_max_right _ _) (fun t ht => by
      have hb : max (Q (2 - t)) 0 ≤ |Q (2 - t)| :=
        max_le (le_abs_self _) (abs_nonneg _)
      linarith [abs_nonneg (Q t)])
    (fun _ _ => le_max_right _ _) (fun t ht => le_min ht.1 hH)
    (fun t ht => overlapProfile_mem_kernelBox hh hcap hMH ht)
    hcost hconj hbudget' hJ (kernelDenominator_nonneg Q) hreturn hpeak

end

end

end ErdosOverlap
