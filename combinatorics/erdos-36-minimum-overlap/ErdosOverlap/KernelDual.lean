/-
Copyright (c) 2026. Released under the BSD-3-Clause license.
-/
module

public import ErdosOverlap.Overlap
public import ErdosOverlap.ContinuousDual

/-!
# Kernel inequalities for actual overlap functions

This file applies the scalar quartet inequality to the positive and negative
overlaps of a measurable admissible partition. It then integrates the
inequality and combines it with the continuous odd-profile dual. Kernel
expectation estimates enter as explicit hypotheses, so this file does not
silently assume any Fourier certificate or numerical lower bound.
-/

namespace ErdosOverlap

open MeasureTheory Set
open scoped Interval

public section

noncomputable section

/-- A common upper bound for both physical overlaps on their full range. -/
@[expose] def OverlapCap (h : ℝ → ℝ) (M : ℝ) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) 2,
    positiveOverlap h t ≤ M ∧ negativeOverlap h t ≤ M

/-- The contribution from a reflected quartet of physical overlaps. -/
@[expose] def quartetIntegrand (h Q : ℝ → ℝ) (t : ℝ) : ℝ :=
  Q t * (positiveOverlap h t + negativeOverlap h t) +
    Q (2 - t) * (positiveOverlap h (2 - t) + negativeOverlap h (2 - t))

/-- The folded even-kernel functional on the actual physical overlaps. -/
@[expose] def quartetFunctional (h Q : ℝ → ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, quartetIntegrand h Q t

/-- Positive kernel mass, in the normalization of the quartet bound. -/
@[expose] def kernelDenominator (Q : ℝ → ℝ) : ℝ :=
  2 * ∫ t in (0 : ℝ)..1, max (Q t) 0 + max (Q (2 - t)) 0

/-- Boundary and odd-profile cost for the auxiliary level `a`. -/
@[expose] def kernelCost (h Q : ℝ → ℝ) (a t : ℝ) : ℝ :=
  profileCost (max (Q (2 - t)) 0) (|Q t| + |Q (2 - t)|)
    (max (2 * a - t) 0) (overlapProfile h t)

/-- The pointwise conjugate used by a continuous kernel/profile witness. -/
@[expose] def kernelConjugate (Q : ℝ → ℝ) (a H τ : ℝ) (v : ℝ → ℝ) (t : ℝ) : ℝ :=
  profileConjugate (max (Q (2 - t)) 0) (|Q t| + |Q (2 - t)|)
    (max (2 * a - t) 0) (min t H) (dualSlope τ v t)

theorem OverlapCap.mono {h : ℝ → ℝ} {M H : ℝ}
    (hcap : OverlapCap h M) (hMH : M ≤ H) : OverlapCap h H := by
  intro t ht
  exact ⟨(hcap t ht).1.trans hMH, (hcap t ht).2.trans hMH⟩

theorem OverlapCap.nonneg {h : ℝ → ℝ} {M : ℝ}
    (hcap : OverlapCap h M) (hh : Admissible h) : 0 ≤ M := by
  exact (positiveOverlap_nonneg hh (by norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) 2)).trans
    (hcap 0 (by norm_num)).1

/-- The odd profile is bounded by any common cap for the two overlaps. -/
theorem overlapProfile_abs_le_cap {h : ℝ → ℝ} {M t : ℝ}
    (hh : Admissible h) (hcap : OverlapCap h M)
    (ht : t ∈ Icc (0 : ℝ) 2) : |overlapProfile h t| ≤ M := by
  rw [← overlap_difference_eq_profile hh ht]
  have hp := positiveOverlap_nonneg hh ht
  have hn := negativeOverlap_nonneg hh ht
  have hc := hcap t ht
  apply abs_le.mpr
  constructor <;> linarith [hc.1, hc.2]

/-- The sum of two overlaps lies in the segment determined by their
absolute difference and the common overlap cap. -/
theorem overlap_pair_segment {h : ℝ → ℝ} {M t : ℝ}
    (hh : Admissible h) (hcap : OverlapCap h M)
    (ht : t ∈ Icc (0 : ℝ) 2) :
    |overlapProfile h t| ≤ positiveOverlap h t + negativeOverlap h t ∧
      positiveOverlap h t + negativeOverlap h t ≤ 2 * M - |overlapProfile h t| := by
  rw [← overlap_difference_eq_profile hh ht]
  have hp := positiveOverlap_nonneg hh ht
  have hn := negativeOverlap_nonneg hh ht
  have hc := hcap t ht
  constructor
  · exact abs_le.mpr ⟨by linarith, by linarith⟩
  · have hdiff : |positiveOverlap h t - negativeOverlap h t| ≤
        2 * M - (positiveOverlap h t + negativeOverlap h t) :=
      abs_le.mpr ⟨by linarith [hc.2], by linarith [hc.1]⟩
    linarith

/-- Clipping before subtracting a nonnegative amount leaves the final
positive part unchanged. -/
theorem positive_part_sub_nonneg (x u : ℝ) (hu : 0 ≤ u) :
    max (max x 0 - u) 0 = max (x - u) 0 := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [max_eq_right hx', max_eq_right (by linarith : 0 - u ≤ 0),
      max_eq_right (by linarith : x - u ≤ 0)]

/-- Monotonicity of the profile cost in its boundary-capacity parameter. -/
theorem profileCost_mono_L {b c L₁ L₂ z : ℝ}
    (hb : 0 ≤ b) (hL : L₁ ≤ L₂) :
    profileCost b c L₁ z ≤ profileCost b c L₂ z := by
  unfold profileCost
  exact add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (max_le_max (sub_le_sub_right hL _) le_rfl) hb)

theorem kernelCost_mono {h Q : ℝ → ℝ} {a M t : ℝ} (haM : a ≤ M) :
    kernelCost h Q a t ≤ kernelCost h Q M t := by
  apply profileCost_mono_L (le_max_right _ _)
  exact max_le_max (by linarith) le_rfl

/-- Pointwise quartet inequality applied to the actual four physical
overlaps, including the boundary cap on the reflected pair. -/
theorem quartet_integrand_add_cost_le {h Q : ℝ → ℝ} {M t : ℝ}
    (hh : Admissible h) (hcap : OverlapCap h M)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    quartetIntegrand h Q t + kernelCost h Q M t ≤
      2 * M * (max (Q t) 0 + max (Q (2 - t)) 0) := by
  have ht₂ : t ∈ Icc (0 : ℝ) 2 := ⟨ht.1, by linarith [ht.2]⟩
  have htr : 2 - t ∈ Icc (0 : ℝ) 2 :=
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hp := overlap_pair_segment hh hcap ht₂
  have hr := overlap_pair_segment hh hcap htr
  rw [overlapProfile_reflection hh ht₂] at hr
  have hboundary : positiveOverlap h (2 - t) + negativeOverlap h (2 - t) ≤ t := by
    have h := overlap_boundary_capacity hh htr
    linarith
  have hquartet := quartet_upper_bound
    (A := Q t) (B := Q (2 - t))
    (s := positiveOverlap h t + negativeOverlap h t)
    (V := positiveOverlap h (2 - t) + negativeOverlap h (2 - t))
    (M := M) (t := t) (u := |overlapProfile h t|)
    (abs_nonneg _) hp.1 hp.2 hr.1 (le_min hr.2 hboundary)
  dsimp [quartetIntegrand, kernelCost, profileCost]
  rw [positive_part_sub_nonneg (2 * M - t) |overlapProfile h t| (abs_nonneg _)]
  linarith

/-- Any auxiliary level below the overlap cap gives a valid weaker cost. -/
theorem quartet_integrand_add_aux_cost_le {h Q : ℝ → ℝ} {a M t : ℝ}
    (hh : Admissible h) (hcap : OverlapCap h M) (haM : a ≤ M)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    quartetIntegrand h Q t + kernelCost h Q a t ≤
      2 * M * (max (Q t) 0 + max (Q (2 - t)) 0) := by
  calc
    quartetIntegrand h Q t + kernelCost h Q a t ≤
        quartetIntegrand h Q t + kernelCost h Q M t :=
      add_le_add le_rfl (kernelCost_mono (h := h) (Q := Q) (t := t) haM)
    _ ≤ _ := quartet_integrand_add_cost_le hh hcap ht

theorem kernelDenominator_nonneg (Q : ℝ → ℝ) : 0 ≤ kernelDenominator Q := by
  unfold kernelDenominator
  have h : 0 ≤ ∫ t in (0 : ℝ)..1, max (Q t) 0 + max (Q (2 - t)) 0 := by
    apply intervalIntegral.integral_nonneg zero_le_one
    intro t ht
    exact add_nonneg (le_max_right _ _) (le_max_right _ _)
  linarith

/-- Integrated physical kernel inequality. The only analytic side conditions
are explicit integrability of the displayed functions. -/
theorem quartet_functional_add_cost_le {h Q : ℝ → ℝ} {a M : ℝ}
    (hh : Admissible h) (hcap : OverlapCap h M) (haM : a ≤ M)
    (hquartet : IntervalIntegrable (quartetIntegrand h Q) volume 0 1)
    (hcost : IntervalIntegrable (kernelCost h Q a) volume 0 1)
    (hpositive : IntervalIntegrable
      (fun t => max (Q t) 0 + max (Q (2 - t)) 0) volume 0 1) :
    quartetFunctional h Q + (∫ t in (0 : ℝ)..1, kernelCost h Q a t) ≤
      M * kernelDenominator Q := by
  have hint := intervalIntegral.integral_mono_on zero_le_one
    (hquartet.add hcost) (hpositive.const_mul (2 * M))
    (fun t ht => quartet_integrand_add_aux_cost_le hh hcap haM ht)
  rw [intervalIntegral.integral_add hquartet hcost,
    intervalIntegral.integral_const_mul] at hint
  unfold quartetFunctional kernelDenominator
  nlinarith

/-- The clipped box available for the physical odd profile. -/
theorem overlapProfile_mem_kernelBox {h : ℝ → ℝ} {M H t : ℝ}
    (hh : Admissible h) (hcap : OverlapCap h M) (hMH : M ≤ H)
    (ht : t ∈ Icc (0 : ℝ) 1) : |overlapProfile h t| ≤ min t H := by
  have ht₂ : t ∈ Icc (0 : ℝ) 2 := ⟨ht.1, by linarith [ht.2]⟩
  exact le_min (overlapProfile_abs_le_time hh ht₂)
    ((overlapProfile_abs_le_cap hh hcap ht₂).trans hMH)

/-- A genuine kernel/profile lower inequality for every admissible relaxed
partition. An arbitrary proved kernel-expectation lower bound may be inserted
as `hell`; no special numerical value is presumed. -/
theorem kernel_profile_lower_bound {h Q v : ℝ → ℝ} {a M H ell τ : ℝ}
    (hh : Admissible h) (hcap : OverlapCap h M)
    (haM : a ≤ M) (hMH : M ≤ H)
    (hv : AbsolutelyContinuousOnInterval v 0 1) (hv1 : v 1 = 0)
    (hquartet : IntervalIntegrable (quartetIntegrand h Q) volume 0 1)
    (hcost : IntervalIntegrable (kernelCost h Q a) volume 0 1)
    (hpositive : IntervalIntegrable
      (fun t => max (Q t) 0 + max (Q (2 - t)) 0) volume 0 1)
    (hconj : IntervalIntegrable (kernelConjugate Q a H τ v) volume 0 1)
    (hell : ell ≤ quartetFunctional h Q) :
    ell + τ * profileMean (overlapProfile h) - (∫ t in (0 : ℝ)..1, |v t|) +
      (∫ t in (0 : ℝ)..1, kernelConjugate Q a H τ v t) ≤
      M * kernelDenominator Q := by
  have hH : 0 ≤ H := (hcap.nonneg hh).trans hMH
  have hdual := interval_profile_dual
    (b := fun t => max (Q (2 - t)) 0)
    (c := fun t => |Q t| + |Q (2 - t)|)
    (L := fun t => max (2 * a - t) 0)
    (U := fun t => min t H)
    (d := overlapProfile h) (v := v) τ
    (overlapProfile_lipschitz hh) hv (overlapProfile_zero h) hv1
    (fun _ _ => le_max_right _ _) (fun t ht => by
      have hb : max (Q (2 - t)) 0 ≤ |Q (2 - t)| :=
        max_le (le_abs_self _) (abs_nonneg _)
      linarith [abs_nonneg (Q t)])
    (fun _ _ => le_max_right _ _) (fun t ht => le_min ht.1 hH)
    (fun t ht => overlapProfile_mem_kernelBox hh hcap hMH ht) hcost hconj
  have hkernel := quartet_functional_add_cost_le hh hcap haM hquartet hcost hpositive
  change τ * profileMean (overlapProfile h) - (∫ t in (0 : ℝ)..1, |v t|) +
      (∫ t in (0 : ℝ)..1, kernelConjugate Q a H τ v t) ≤
      ∫ t in (0 : ℝ)..1, kernelCost h Q a t at hdual
  linarith

/-- Fixed-target form. Only `a ≤ T` is required for the auxiliary level;
there is deliberately no assumption `a ≤ M`. Thus it is valid inside a
contradiction argument testing whether the true overlap cap is at most `T`. -/
theorem fixed_target_kernel_profile_bound {h Q v : ℝ → ℝ} {a M T H ell τ : ℝ}
    (hh : Admissible h) (hcap : OverlapCap h M)
    (hMT : M ≤ T) (haT : a ≤ T) (hTH : T ≤ H)
    (hv : AbsolutelyContinuousOnInterval v 0 1) (hv1 : v 1 = 0)
    (hquartet : IntervalIntegrable (quartetIntegrand h Q) volume 0 1)
    (hcost : IntervalIntegrable (kernelCost h Q a) volume 0 1)
    (hpositive : IntervalIntegrable
      (fun t => max (Q t) 0 + max (Q (2 - t)) 0) volume 0 1)
    (hconj : IntervalIntegrable (kernelConjugate Q a H τ v) volume 0 1)
    (hell : ell ≤ quartetFunctional h Q) :
    ell + τ * profileMean (overlapProfile h) - (∫ t in (0 : ℝ)..1, |v t|) +
      (∫ t in (0 : ℝ)..1, kernelConjugate Q a H τ v t) ≤
      T * kernelDenominator Q := by
  exact kernel_profile_lower_bound hh (hcap.mono hMT) haT hTH hv hv1
    hquartet hcost hpositive hconj hell

/-- Dividing the physical kernel inequality by a positive denominator gives
the usual lower-bound normalization. -/
theorem kernel_profile_lower_bound_div {h Q v : ℝ → ℝ} {a M H ell τ : ℝ}
    (hh : Admissible h) (hcap : OverlapCap h M)
    (haM : a ≤ M) (hMH : M ≤ H)
    (hv : AbsolutelyContinuousOnInterval v 0 1) (hv1 : v 1 = 0)
    (hquartet : IntervalIntegrable (quartetIntegrand h Q) volume 0 1)
    (hcost : IntervalIntegrable (kernelCost h Q a) volume 0 1)
    (hpositive : IntervalIntegrable
      (fun t => max (Q t) 0 + max (Q (2 - t)) 0) volume 0 1)
    (hconj : IntervalIntegrable (kernelConjugate Q a H τ v) volume 0 1)
    (hell : ell ≤ quartetFunctional h Q) (hD : 0 < kernelDenominator Q) :
    (ell + τ * profileMean (overlapProfile h) - (∫ t in (0 : ℝ)..1, |v t|) +
      (∫ t in (0 : ℝ)..1, kernelConjugate Q a H τ v t)) /
        kernelDenominator Q ≤ M := by
  apply (div_le_iff₀ hD).mpr
  exact kernel_profile_lower_bound hh hcap haM hMH hv hv1
    hquartet hcost hpositive hconj hell

/-- A strict certified witness excludes the tested overlap cap. This form
requires only `a ≤ T`; no previously established lower bound is used. -/
theorem not_overlapCap_of_kernel_profile_witness
    {h Q v : ℝ → ℝ} {a T H ell τ : ℝ}
    (hh : Admissible h) (haT : a ≤ T) (hTH : T ≤ H)
    (hv : AbsolutelyContinuousOnInterval v 0 1) (hv1 : v 1 = 0)
    (hquartet : IntervalIntegrable (quartetIntegrand h Q) volume 0 1)
    (hcost : IntervalIntegrable (kernelCost h Q a) volume 0 1)
    (hpositive : IntervalIntegrable
      (fun t => max (Q t) 0 + max (Q (2 - t)) 0) volume 0 1)
    (hconj : IntervalIntegrable (kernelConjugate Q a H τ v) volume 0 1)
    (hell : ell ≤ quartetFunctional h Q)
    (hstrict : T * kernelDenominator Q <
      ell + τ * profileMean (overlapProfile h) - (∫ t in (0 : ℝ)..1, |v t|) +
        (∫ t in (0 : ℝ)..1, kernelConjugate Q a H τ v t)) :
    ¬ OverlapCap h T := by
  intro hcap
  exact (not_lt_of_ge (kernel_profile_lower_bound hh hcap haT hTH hv hv1
    hquartet hcost hpositive hconj hell)) hstrict

end

end

end ErdosOverlap
