/-
Copyright (c) 2026. Released under the BSD-3-Clause license.
-/
module

public import ErdosOverlap.KernelLinearity

/-!
# Physical bounds for signed kernels

Outer mean intervals use kernels which need not be even. Their pairing
is taken with the actual signed overlap, and their positive mass is
integrated over the whole difference interval `[-2,2]`.
-/

namespace ErdosOverlap
open MeasureTheory Set
open scoped Interval
public section
noncomputable section

@[expose] def signedKernelDenominator (Q : ℝ → ℝ) : ℝ :=
  ∫ t in (-2 : ℝ)..2, max (Q t) 0

theorem signedOverlapIntegrand_intervalIntegrable_of_boundedOn
    {h Q : ℝ → ℝ} {C : ℝ} (hh : Admissible h)
    (hQ : Measurable Q) (hbound : ∀ t ∈ Icc (-2 : ℝ) 2, |Q t| ≤ C) :
    IntervalIntegrable (signedOverlapIntegrand h Q) volume 0 2 := by
  let J := (Icc (-2 : ℝ) 2).indicator Q
  have hC : 0 ≤ C := (abs_nonneg (Q 0)).trans (hbound 0 (by norm_num))
  have hb : ∀ t, |J t| ≤ C := by
    intro t
    by_cases ht : t ∈ Icc (-2 : ℝ) 2
    · simpa only [J, indicator_of_mem ht] using hbound t ht
    · simpa only [J, indicator_of_notMem ht, abs_zero] using hC
  apply (signedOverlapIntegrand_intervalIntegrable hh (hQ.indicator measurableSet_Icc) hb).congr_uIoo
  intro t ht
  rw [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
  have ht' : t ∈ Icc (-2 : ℝ) 2 := ⟨by linarith [ht.1], ht.2.le⟩
  have hn : -t ∈ Icc (-2 : ℝ) 2 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  simp only [signedOverlapIntegrand, indicator_of_mem ht', indicator_of_mem hn]

theorem signedOverlapIntegrand_intervalIntegrable_of_continuous
    {h Q : ℝ → ℝ} (hh : Admissible h) (hQ : Continuous Q) :
    IntervalIntegrable (signedOverlapIntegrand h Q) volume 0 2 := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (-2 : ℝ) 2)).exists_bound_of_continuousOn
    hQ.continuousOn
  exact signedOverlapIntegrand_intervalIntegrable_of_boundedOn hh hQ.measurable
    (by simpa only [Real.norm_eq_abs] using hC)

theorem signedOverlapIntegrand_add (h Q J : ℝ → ℝ) (t : ℝ) :
    signedOverlapIntegrand h (fun x => Q x + J x) t =
      signedOverlapIntegrand h Q t + signedOverlapIntegrand h J t := by
  unfold signedOverlapIntegrand
  ring

theorem signedOverlapIntegrand_mul (h Q : ℝ → ℝ) (c t : ℝ) :
    signedOverlapIntegrand h (fun x => c * Q x) t = c * signedOverlapIntegrand h Q t := by
  unfold signedOverlapIntegrand
  ring

theorem squarePairing_add {h Q J : ℝ → ℝ} (hh : Admissible h)
    (hQ : Continuous Q) (hJ : Continuous J) :
    squarePairing h (fun t => Q t + J t) = squarePairing h Q + squarePairing h J := by
  rw [squarePairing_eq_signedOverlapPairing_of_continuous (K := fun t => Q t + J t) hh (hQ.add hJ),
    squarePairing_eq_signedOverlapPairing_of_continuous hh hQ,
    squarePairing_eq_signedOverlapPairing_of_continuous hh hJ]
  simp only [signedOverlapPairing, signedOverlapIntegrand_add]
  exact intervalIntegral.integral_add
    (signedOverlapIntegrand_intervalIntegrable_of_continuous hh hQ)
    (signedOverlapIntegrand_intervalIntegrable_of_continuous hh hJ)

theorem squarePairing_mul {h Q : ℝ → ℝ} (hh : Admissible h)
    (hQ : Continuous Q) (c : ℝ) :
    squarePairing h (fun t => c * Q t) = c * squarePairing h Q := by
  rw [squarePairing_eq_signedOverlapPairing_of_continuous (K := fun t => c * Q t) hh (continuous_const.mul hQ),
    squarePairing_eq_signedOverlapPairing_of_continuous hh hQ]
  simp only [signedOverlapPairing, signedOverlapIntegrand_mul, intervalIntegral.integral_const_mul]

theorem squarePairing_sub {h Q J : ℝ → ℝ} (hh : Admissible h)
    (hQ : Continuous Q) (hJ : Continuous J) :
    squarePairing h (fun t => Q t - J t) = squarePairing h Q - squarePairing h J := by
  have heq : (fun t => Q t - J t) = (fun t => Q t + (-1) * J t) := by funext t; ring
  rw [heq, squarePairing_add (Q := Q) (J := fun t => (-1) * J t) hh hQ
    (continuous_const.mul hJ), squarePairing_mul hh hJ]
  ring

theorem squarePairing_const {h : ℝ → ℝ} (hh : Admissible h) (c : ℝ) :
    squarePairing h (fun _ => c) = c := by
  have heq : (fun _ : ℝ => c) = (fun _ : ℝ => c * 1) := by funext t; ring
  rw [heq, squarePairing_mul hh continuous_const, squarePairing_one hh, mul_one]

theorem scalar_weighted_cap {q p M : ℝ} (hp : 0 ≤ p) (hpM : p ≤ M) :
    q * p ≤ M * max q 0 := by
  by_cases hq : 0 ≤ q
  · rw [max_eq_left hq, mul_comm M q]
    exact mul_le_mul_of_nonneg_left hpM hq
  · rw [max_eq_right (le_of_not_ge hq), mul_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hq) hp

theorem signedKernelDenominator_fold {Q : ℝ → ℝ} (hQ : Continuous Q) :
    signedKernelDenominator Q = ∫ t in (0 : ℝ)..2, max (Q t) 0 + max (Q (-t)) 0 := by
  have hp : Continuous (fun t => max (Q t) 0) := hQ.max continuous_const
  have hn : (∫ t in (-2 : ℝ)..0, max (Q t) 0) =
      ∫ t in (0 : ℝ)..2, max (Q (-t)) 0 := by
    simpa only [zero_sub, sub_zero] using
      (intervalIntegral.integral_comp_sub_left (fun t => max (Q t) 0) (a := 0) (b := 2) 0).symm
  rw [signedKernelDenominator, ← intervalIntegral.integral_add_adjacent_intervals
    (hp.intervalIntegrable (a := -2) (b := 0)) (hp.intervalIntegrable (a := 0) (b := 2)), hn,
    intervalIntegral.integral_add (f := fun t => max (Q t) 0)
      (g := fun t => max (Q (-t)) 0) (hp.intervalIntegrable 0 2)
      ((hp.comp continuous_neg).intervalIntegrable 0 2)]
  exact add_comm _ _

/-- The common physical overlap cap controls any continuous signed kernel. -/
theorem squarePairing_le_cap {h Q : ℝ → ℝ} {M : ℝ}
    (hh : Admissible h) (hcap : OverlapCap h M) (hQ : Continuous Q) :
    squarePairing h Q ≤ M * signedKernelDenominator Q := by
  rw [squarePairing_eq_signedOverlapPairing_of_continuous hh hQ, signedKernelDenominator_fold hQ]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 2)
    (signedOverlapIntegrand_intervalIntegrable_of_continuous hh hQ)
    ((continuous_const.mul ((hQ.max continuous_const).add
      ((hQ.comp continuous_neg).max continuous_const))).intervalIntegrable 0 2)
  intro t ht
  unfold signedOverlapIntegrand
  change Q t * positiveOverlap h t + Q (-t) * negativeOverlap h t ≤
    M * (max (Q t) 0 + max (Q (-t)) 0)
  have hc := hcap t ht
  have hp := scalar_weighted_cap (q := Q t) (positiveOverlap_nonneg hh ht) hc.1
  have hn := scalar_weighted_cap (q := Q (-t)) (negativeOverlap_nonneg hh ht) hc.2
  nlinarith

theorem signedKernelDenominator_nonneg (Q : ℝ → ℝ) : 0 ≤ signedKernelDenominator Q := by
  apply intervalIntegral.integral_nonneg (by norm_num : (-2 : ℝ) ≤ 2)
  intro t _
  exact le_max_right _ _

theorem squarePairing_id_eq_mean {h : ℝ → ℝ} (hh : Admissible h) :
    squarePairing h (fun t => t) = profileMean (overlapProfile h) := by
  rw [squarePairing_id hh, profileMean_eq_densityFirstMoment hh]

theorem squarePairing_sq_eq_mean {h : ℝ → ℝ} (hh : Admissible h) :
    squarePairing h (fun t => t^2) = 2/3 + profileMean (overlapProfile h)^2/2 := by
  rw [squarePairing_eq_quartetFunctional_of_continuous (K := fun t : ℝ => t^2) hh (continuous_id.pow 2)
    (fun t => by simp), quartetFunctional_sq hh]

end
end
end ErdosOverlap
