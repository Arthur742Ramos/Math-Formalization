module

public import ErdosOverlap.Overlap
public import ErdosOverlap.ContinuousDual
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # The physical first moment and the folded profile -/

namespace ErdosOverlap

open MeasureTheory Set
open scoped Interval

public section
noncomputable section

/-- First moment of the signed overlap distribution, using its two halves. -/
@[expose] def overlapFirstMoment (h : ℝ → ℝ) : ℝ :=
  ∫ t in (0:ℝ)..2, t * (positiveOverlap h t - negativeOverlap h t)

theorem intervalIntegral_id_zero_one : (∫ t in (0:ℝ)..1, t) = 1/2 := by
  have hp : ∀ t ∈ uIcc (0:ℝ) 1,
      HasDerivAt (fun x : ℝ => x*x/2) t t := by
    intro t _
    convert ((hasDerivAt_id t).mul (hasDerivAt_id t)).div_const 2 using 1
    all_goals dsimp only [id_eq, Pi.mul_apply]
    all_goals ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hp
    (continuous_id.intervalIntegrable 0 1)
  norm_num at hi ⊢
  exact hi

theorem overlapProfile_intervalIntegrable {h : ℝ → ℝ} (hh : Admissible h)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 2) :
    IntervalIntegrable (overlapProfile h) volume a b := by
  have hc := (overlapProfile_lipschitz_full hh).continuousOn
  apply ContinuousOn.intervalIntegrable
  apply hc.mono
  rw [uIcc_of_le hab]
  intro x hx
  exact ⟨ha.trans hx.1, hx.2.trans hb⟩

/-- The folded definition of the mean is equal to the physical first moment. -/
theorem overlapFirstMoment_eq_profileMean {h : ℝ → ℝ} (hh : Admissible h) :
    overlapFirstMoment h = profileMean (overlapProfile h) := by
  have hd : ContinuousOn (overlapProfile h) (uIcc (0:ℝ) 2) := by
    simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 2)] using
      (overlapProfile_lipschitz_full hh).continuousOn
  have ht : IntervalIntegrable (fun x => x * overlapProfile h x) volume 0 2 :=
    (continuous_id.continuousOn.mul hd).intervalIntegrable
  have ht01 : IntervalIntegrable (fun x => x * overlapProfile h x) volume 0 1 := by
    apply ht.mono_set
    simp only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1),
      uIcc_of_le (by norm_num : (0:ℝ) ≤ 2)]
    intro x hx
    exact ⟨hx.1, by linarith [hx.2]⟩
  have ht12 : IntervalIntegrable (fun x => x * overlapProfile h x) volume 1 2 := by
    apply ht.mono_set
    simp only [uIcc_of_le (by norm_num : (1:ℝ) ≤ 2),
      uIcc_of_le (by norm_num : (0:ℝ) ≤ 2)]
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  have hr : IntervalIntegrable (fun x => (2-x) * overlapProfile h x) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    apply (continuous_const.sub continuous_id).continuousOn.mul
    apply hd.mono
    simp only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1),
      uIcc_of_le (by norm_num : (0:ℝ) ≤ 2)]
    intro x hx
    exact ⟨hx.1, by linarith [hx.2]⟩
  have hreflect : (∫ x in (1:ℝ)..2, x * overlapProfile h x) =
      ∫ x in (0:ℝ)..1, (2-x) * overlapProfile h x := by
    have hc := intervalIntegral.integral_comp_sub_left
      (fun x => x * overlapProfile h x) (a := 0) (b := 1) 2
    norm_num at hc
    rw [← hc]
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Icc (0:ℝ) 2 := by
      rw [uIcc_of_le zero_le_one] at hx
      exact ⟨hx.1, by linarith [hx.2]⟩
    change (2-x) * overlapProfile h (2-x) = (2-x) * overlapProfile h x
    rw [overlapProfile_reflection hh hx']
  calc
    overlapFirstMoment h = ∫ t in (0:ℝ)..2, t * overlapProfile h t := by
      apply intervalIntegral.integral_congr
      intro t ht'
      rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 2)] at ht'
      change t * (positiveOverlap h t - negativeOverlap h t) = t * overlapProfile h t
      rw [overlap_difference_eq_profile hh ht']
    _ = (∫ t in (0:ℝ)..1, t * overlapProfile h t) +
        (∫ t in (1:ℝ)..2, t * overlapProfile h t) :=
      (intervalIntegral.integral_add_adjacent_intervals ht01 ht12).symm
    _ = ∫ t in (0:ℝ)..1, t * overlapProfile h t + (2-t)*overlapProfile h t := by
      rw [hreflect, intervalIntegral.integral_add ht01 hr]
    _ = ∫ t in (0:ℝ)..1, 2*overlapProfile h t := by
      apply intervalIntegral.integral_congr
      intro t _
      ring
    _ = profileMean (overlapProfile h) := by
      rw [intervalIntegral.integral_const_mul]
      rfl

/-- Every physical first moment lies in the interval used by the certificate cover. -/
theorem profileMean_abs_le_one {h : ℝ → ℝ} (hh : Admissible h) :
    |profileMean (overlapProfile h)| ≤ 1 := by
  have hnorm : |∫ t in (0:ℝ)..1, overlapProfile h t| ≤
      ∫ t in (0:ℝ)..1, t := by
    change ‖∫ t in (0:ℝ)..1, overlapProfile h t‖ ≤ ∫ t in (0:ℝ)..1, t
    apply intervalIntegral.norm_integral_le_of_norm_le zero_le_one
      (Filter.Eventually.of_forall (fun t ht => ?_)) (continuous_id.intervalIntegrable 0 1)
    change |overlapProfile h t| ≤ t
    exact overlapProfile_abs_le_time hh ⟨le_of_lt ht.1, by linarith [ht.2]⟩
  rw [intervalIntegral_id_zero_one] at hnorm
  rw [profileMean, abs_mul]
  norm_num
  linarith

theorem overlapFirstMoment_mem {h : ℝ → ℝ} (hh : Admissible h) :
    overlapFirstMoment h ∈ Icc (-1:ℝ) 1 := by
  rw [overlapFirstMoment_eq_profileMean hh]
  exact abs_le.mp (profileMean_abs_le_one hh)

end
end
end ErdosOverlap
