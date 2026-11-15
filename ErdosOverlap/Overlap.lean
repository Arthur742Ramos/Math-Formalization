module

public import ErdosOverlap.Pointwise
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Geometry of a measurable relaxed partition

The two overlap functions below are the positive and negative translates of
the two colours on `[0,2]`.  All bounds in this file hold for measurable
relaxed partitions, not only for step functions or binary partitions.
-/

namespace ErdosOverlap

open MeasureTheory Set
open scoped Interval

public section

/-- A measurable relaxed partition into two colours of equal mass. -/
structure Admissible (h : ℝ → ℝ) : Prop where
  measurable : Measurable h
  nonneg : ∀ x ∈ Icc (0 : ℝ) 2, 0 ≤ h x
  le_one : ∀ x ∈ Icc (0 : ℝ) 2, h x ≤ 1
  mass : (∫ x in (0 : ℝ)..2, h x) = 1

/-- Overlap with the second colour translated by a nonnegative displacement. -/
@[expose] noncomputable def positiveOverlap (h : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..(2-t), h x * (1-h (x+t))

/-- Overlap at the negative of a nonnegative displacement. -/
@[expose] noncomputable def negativeOverlap (h : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..(2-t), h (x+t) * (1-h x)

/-- The derivative density of the odd overlap profile. -/
@[expose] def profileSlope (h : ℝ → ℝ) (x : ℝ) : ℝ := h x - h (2-x)

/-- The primitive representation of the odd overlap profile. -/
@[expose] noncomputable def overlapProfile (h : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..t, profileSlope h x

theorem intervalIntegrable_of_abs_le {f : ℝ → ℝ} {a b C : ℝ}
    (hf : Measurable f) (hab : a ≤ b) (hC : 0 ≤ C)
    (hbound : ∀ x ∈ Icc a b, |f x| ≤ C) :
    IntervalIntegrable f volume a b := by
  refine (intervalIntegrable_const (c := C)).mono_fun hf.aestronglyMeasurable ?_
  rw [uIoc_of_le hab]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with x hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg hC] using
    hbound x ⟨le_of_lt hx.1, hx.2⟩

theorem Admissible.intervalIntegrable {h : ℝ → ℝ} (hh : Admissible h)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 2) :
    IntervalIntegrable h volume a b := by
  apply intervalIntegrable_of_abs_le hh.measurable hab (by norm_num : (0:ℝ) ≤ 1)
  intro x hx
  have hx' : x ∈ Icc (0:ℝ) 2 := ⟨ha.trans hx.1, hx.2.trans hb⟩
  simpa only [abs_of_nonneg (hh.nonneg x hx')] using hh.le_one x hx'

theorem Admissible.positiveIntegrable {h : ℝ → ℝ} (hh : Admissible h)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 2) :
    IntervalIntegrable (fun x => h x * (1-h (x+t))) volume 0 (2-t) := by
  apply intervalIntegrable_of_abs_le
    (hh.measurable.mul (measurable_const.sub
      (hh.measurable.comp (measurable_id.add_const t)))) (by linarith [ht.2])
      (by norm_num : (0:ℝ) ≤ 1)
  intro x hx
  have hx' : x ∈ Icc (0:ℝ) 2 := ⟨hx.1, by linarith [hx.2, ht.1]⟩
  have hxt : x+t ∈ Icc (0:ℝ) 2 := ⟨by linarith [hx.1, ht.1], by linarith [hx.2]⟩
  have hp : 0 ≤ h x * (1-h (x+t)) :=
    mul_nonneg (hh.nonneg x hx') (by linarith [hh.le_one (x+t) hxt])
  change |h x * (1-h (x+t))| ≤ 1
  rw [abs_of_nonneg hp]
  nlinarith [hh.nonneg x hx', hh.le_one x hx', hh.nonneg (x+t) hxt,
    hh.le_one (x+t) hxt]

theorem Admissible.negativeIntegrable {h : ℝ → ℝ} (hh : Admissible h)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 2) :
    IntervalIntegrable (fun x => h (x+t) * (1-h x)) volume 0 (2-t) := by
  apply intervalIntegrable_of_abs_le
    ((hh.measurable.comp (measurable_id.add_const t)).mul
      (measurable_const.sub hh.measurable)) (by linarith [ht.2])
      (by norm_num : (0:ℝ) ≤ 1)
  intro x hx
  have hx' : x ∈ Icc (0:ℝ) 2 := ⟨hx.1, by linarith [hx.2, ht.1]⟩
  have hxt : x+t ∈ Icc (0:ℝ) 2 := ⟨by linarith [hx.1, ht.1], by linarith [hx.2]⟩
  have hp : 0 ≤ h (x+t) * (1-h x) :=
    mul_nonneg (hh.nonneg (x+t) hxt) (by linarith [hh.le_one x hx'])
  change |h (x+t) * (1-h x)| ≤ 1
  rw [abs_of_nonneg hp]
  nlinarith [hh.nonneg x hx', hh.le_one x hx', hh.nonneg (x+t) hxt,
    hh.le_one (x+t) hxt]

theorem positiveOverlap_nonneg {h : ℝ → ℝ} (hh : Admissible h)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 2) : 0 ≤ positiveOverlap h t := by
  apply intervalIntegral.integral_nonneg (by linarith [ht.2])
  intro x hx
  have hx' : x ∈ Icc (0:ℝ) 2 := ⟨hx.1, by linarith [hx.2, ht.1]⟩
  have hxt : x+t ∈ Icc (0:ℝ) 2 := ⟨by linarith [hx.1, ht.1], by linarith [hx.2]⟩
  exact mul_nonneg (hh.nonneg x hx') (by linarith [hh.le_one (x+t) hxt])

theorem negativeOverlap_nonneg {h : ℝ → ℝ} (hh : Admissible h)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 2) : 0 ≤ negativeOverlap h t := by
  apply intervalIntegral.integral_nonneg (by linarith [ht.2])
  intro x hx
  have hx' : x ∈ Icc (0:ℝ) 2 := ⟨hx.1, by linarith [hx.2, ht.1]⟩
  have hxt : x+t ∈ Icc (0:ℝ) 2 := ⟨by linarith [hx.1, ht.1], by linarith [hx.2]⟩
  exact mul_nonneg (hh.nonneg (x+t) hxt) (by linarith [hh.le_one x hx'])

/-- Exact boundary capacity: the two signed overlaps sum to at most `2-t`. -/
theorem overlap_boundary_capacity {h : ℝ → ℝ} (hh : Admissible h)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 2) :
    positiveOverlap h t + negativeOverlap h t ≤ 2-t := by
  have hi := (hh.positiveIntegrable ht).add (hh.negativeIntegrable ht)
  unfold positiveOverlap negativeOverlap
  rw [← intervalIntegral.integral_add (hh.positiveIntegrable ht) (hh.negativeIntegrable ht)]
  calc
    _ ≤ ∫ _x in (0:ℝ)..(2-t), (1:ℝ) := by
      apply intervalIntegral.integral_mono_on (by linarith [ht.2]) hi intervalIntegrable_const
      intro x hx
      have hx' : x ∈ Icc (0:ℝ) 2 := ⟨hx.1, by linarith [hx.2, ht.1]⟩
      have hxt : x+t ∈ Icc (0:ℝ) 2 := ⟨by linarith [hx.1, ht.1], by linarith [hx.2]⟩
      have hpair := boundary_pair_le_one (hh.nonneg x hx') (hh.le_one x hx')
        (hh.nonneg (x+t) hxt) (hh.le_one (x+t) hxt)
      nlinarith
    _ = 2-t := by simp

theorem profileSlope_measurable {h : ℝ → ℝ} (hh : Admissible h) :
    Measurable (profileSlope h) :=
  hh.measurable.sub (hh.measurable.comp (measurable_const.sub measurable_id))

theorem profileSlope_abs_le_one {h : ℝ → ℝ} (hh : Admissible h)
    {x : ℝ} (hx : x ∈ Icc (0:ℝ) 2) : |profileSlope h x| ≤ 1 := by
  have hx' : 2-x ∈ Icc (0:ℝ) 2 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  unfold profileSlope
  exact abs_le.mpr ⟨by linarith [hh.nonneg x hx, hh.le_one (2-x) hx'],
    by linarith [hh.le_one x hx, hh.nonneg (2-x) hx']⟩

theorem profileSlope_intervalIntegrable {h : ℝ → ℝ} (hh : Admissible h)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 2) :
    IntervalIntegrable (profileSlope h) volume a b := by
  apply intervalIntegrable_of_abs_le (profileSlope_measurable hh) hab (by norm_num : (0:ℝ) ≤ 1)
  intro x hx
  exact profileSlope_abs_le_one hh ⟨ha.trans hx.1, hx.2.trans hb⟩

@[simp] theorem overlapProfile_zero (h : ℝ → ℝ) : overlapProfile h 0 = 0 := by
  simp [overlapProfile]

theorem overlapProfile_cumulative {h : ℝ → ℝ} (hh : Admissible h)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 2) :
    overlapProfile h t = (∫ x in (0:ℝ)..t, h x) +
      (∫ x in (0:ℝ)..(2-t), h x) - 1 := by
  have hi := hh.intervalIntegrable (a := 0) (b := t) (by norm_num) ht.1 ht.2
  have hi' := hh.intervalIntegrable (a := 2-t) (b := 2)
    (by linarith [ht.2]) (by linarith [ht.1]) le_rfl
  have hir : IntervalIntegrable (fun x => h (2-x)) volume 0 t := by
    simpa using (hi'.comp_sub_left 2).symm
  have him := hh.intervalIntegrable (a := 0) (b := 2-t)
    (by norm_num) (by linarith [ht.2]) (by linarith [ht.1])
  have hadd := intervalIntegral.integral_add_adjacent_intervals him hi'
  rw [hh.mass] at hadd
  unfold overlapProfile profileSlope
  rw [intervalIntegral.integral_sub hi hir, intervalIntegral.integral_comp_sub_left]
  simp only [sub_zero]
  linarith

/-- The primitive is the actual difference of the signed overlap functions. -/
theorem overlap_difference_eq_profile {h : ℝ → ℝ} (hh : Admissible h)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 2) :
    positiveOverlap h t - negativeOverlap h t = overlapProfile h t := by
  have hi := hh.intervalIntegrable (a := 0) (b := 2-t)
    (by norm_num) (by linarith [ht.2]) (by linarith [ht.1])
  have hit := hh.intervalIntegrable (a := t) (b := 2) ht.1 ht.2 le_rfl
  have hshift : IntervalIntegrable (fun x => h (x+t)) volume 0 (2-t) := by
    simpa using hit.comp_add_right t
  have hi0t := hh.intervalIntegrable (a := 0) (b := t) (by norm_num) ht.1 ht.2
  have hadd := intervalIntegral.integral_add_adjacent_intervals hi0t hit
  rw [hh.mass] at hadd
  unfold positiveOverlap negativeOverlap
  rw [← intervalIntegral.integral_sub (hh.positiveIntegrable ht) (hh.negativeIntegrable ht)]
  calc
    _ = ∫ x in (0:ℝ)..(2-t), h x - h (x+t) := by
      apply intervalIntegral.integral_congr
      intro x _
      ring
    _ = (∫ x in (0:ℝ)..(2-t), h x) - (∫ x in t..2, h x) := by
      rw [intervalIntegral.integral_sub hi hshift, intervalIntegral.integral_comp_add_right]
      simp
    _ = overlapProfile h t := by
      rw [overlapProfile_cumulative hh ht]
      linarith

/-- Reflection symmetry of the odd profile. -/
theorem overlapProfile_reflection {h : ℝ → ℝ} (hh : Admissible h)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 2) :
    overlapProfile h (2-t) = overlapProfile h t := by
  have ht' : 2-t ∈ Icc (0:ℝ) 2 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  rw [overlapProfile_cumulative hh ht', overlapProfile_cumulative hh ht]
  simp only [sub_sub_cancel]
  ring

/-- The physical odd profile is 1-Lipschitz on the entire interval. -/
theorem overlapProfile_lipschitz_full {h : ℝ → ℝ} (hh : Admissible h) :
    LipschitzOnWith 1 (overlapProfile h) (Icc (0:ℝ) 2) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hix := profileSlope_intervalIntegrable hh (a := 0) (b := x)
    (by norm_num) hx.1 hx.2
  have hiy := profileSlope_intervalIntegrable hh (a := 0) (b := y)
    (by norm_num) hy.1 hy.2
  have hb : ∀ z ∈ Ι y x, ‖profileSlope h z‖ ≤ (1:ℝ) := by
    intro z hz
    have hz' : z ∈ Icc (0:ℝ) 2 :=
      ⟨(le_min hy.1 hx.1).trans (le_of_lt hz.1), hz.2.trans (max_le hy.2 hx.2)⟩
    simpa only [Real.norm_eq_abs] using profileSlope_abs_le_one hh hz'
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const hb
  simp only [Real.norm_eq_abs, one_mul] at hn
  simp only [Real.dist_eq, NNReal.coe_one, one_mul, overlapProfile]
  rw [intervalIntegral.integral_interval_sub_left hix hiy]
  exact hn

theorem overlapProfile_lipschitz {h : ℝ → ℝ} (hh : Admissible h) :
    LipschitzOnWith 1 (overlapProfile h) (uIcc (0:ℝ) 1) := by
  apply (overlapProfile_lipschitz_full hh).mono
  rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  intro x hx
  exact ⟨hx.1, by linarith [hx.2]⟩

theorem overlapProfile_abs_le_time {h : ℝ → ℝ} (hh : Admissible h)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 2) : |overlapProfile h t| ≤ t := by
  have hl := (overlapProfile_lipschitz_full hh).dist_le_mul t ht 0 (by norm_num)
  simpa only [Real.dist_eq, overlapProfile_zero, sub_zero, NNReal.coe_one, one_mul,
    abs_of_nonneg ht.1] using hl

end
end ErdosOverlap
