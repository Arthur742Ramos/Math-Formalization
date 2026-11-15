/-
Copyright (c) 2026. Released under the BSD-3-Clause license.
-/
module

public import ErdosOverlap.FourierKernel
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Function.Floor

/-!
# Periodic triangle and perimeter inequalities for physical overlaps

The period-two extension is formed from the actual admissible density.
All nine periodic families in the native certificate use the triangle or
perimeter inequality on three translated values of this extension.
-/

namespace ErdosOverlap

open MeasureTheory Set Function
open scoped Interval

public section
noncomputable section

@[expose] def periodicDensity (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  h (toIcoMod (by norm_num : (0 : ℝ) < 2) 0 x)

@[expose] def periodicOverlap (h : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..2, periodicDensity h x * (1 - periodicDensity h (x + s))

@[expose] def pairDisagreement (a b : ℝ) : ℝ := a + b - 2 * a * b

theorem pairDisagreement_triangle {a b c : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) (hc : c ∈ Icc (0 : ℝ) 1) :
    pairDisagreement a c ≤ pairDisagreement a b + pairDisagreement b c := by
  have hp := mul_nonneg (mul_nonneg hb.1 (sub_nonneg.mpr ha.2)) (sub_nonneg.mpr hc.2)
  have hq := mul_nonneg (mul_nonneg (sub_nonneg.mpr hb.2) ha.1) hc.1
  unfold pairDisagreement
  nlinarith

theorem pairDisagreement_perimeter {a b c : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) (hc : c ∈ Icc (0 : ℝ) 1) :
    pairDisagreement a b + pairDisagreement b c + pairDisagreement c a ≤ 2 := by
  have hp := mul_nonneg (mul_nonneg ha.1 hb.1) hc.1
  have hq := mul_nonneg (mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr hb.2))
    (sub_nonneg.mpr hc.2)
  unfold pairDisagreement
  nlinarith

theorem pairDisagreement_nonneg {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    0 ≤ pairDisagreement a b := by
  have hp := mul_nonneg ha.1 (sub_nonneg.mpr hb.2)
  have hq := mul_nonneg hb.1 (sub_nonneg.mpr ha.2)
  unfold pairDisagreement
  nlinarith

theorem pairDisagreement_le_one {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    pairDisagreement a b ≤ 1 := boundary_pair_le_one ha.1 ha.2 hb.1 hb.2

theorem periodicDensity_periodic (h : ℝ → ℝ) : Periodic (periodicDensity h) 2 := by
  intro x
  unfold periodicDensity
  rw [toIcoMod_add_right]

theorem periodicDensity_measurable_of_measurable {h : ℝ → ℝ} (hh : Measurable h) :
    Measurable (periodicDensity h) := by
  have hmod : Measurable (fun x : ℝ => toIcoMod (by norm_num : (0 : ℝ) < 2) 0 x) := by
    simp only [toIcoMod_eq_fract_mul]
    exact (measurable_fract.comp (measurable_id.div_const 2)).mul_const 2
  exact hh.comp hmod

theorem periodicDensity_measurable {h : ℝ → ℝ} (hh : Admissible h) :
    Measurable (periodicDensity h) := periodicDensity_measurable_of_measurable hh.measurable

theorem periodicDensity_mem {h : ℝ → ℝ} (hh : Admissible h) (x : ℝ) :
    periodicDensity h x ∈ Icc (0 : ℝ) 1 := by
  have hx := toIcoMod_mem_Ico' (by norm_num : (0 : ℝ) < 2) x
  exact ⟨hh.nonneg _ ⟨hx.1, hx.2.le⟩, hh.le_one _ ⟨hx.1, hx.2.le⟩⟩

theorem periodicDensity_eq {h : ℝ → ℝ} {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 2) :
    periodicDensity h x = h x := by
  unfold periodicDensity
  rw [(toIcoMod_eq_self (by norm_num : (0 : ℝ) < 2)).mpr (by simpa using hx)]

theorem periodicDensity_intervalIntegrable {h : ℝ → ℝ} (hh : Admissible h) (a b : ℝ) :
    IntervalIntegrable (periodicDensity h) volume a b := by
  wlog hab : a ≤ b
  · exact (this hh b a (le_of_not_ge hab)).symm
  apply intervalIntegrable_of_abs_le (periodicDensity_measurable hh) hab (by norm_num : (0 : ℝ) ≤ 1)
  intro x _
  rw [abs_of_nonneg (periodicDensity_mem hh x).1]
  exact (periodicDensity_mem hh x).2

theorem periodicDensity_mass {h : ℝ → ℝ} (hh : Admissible h) :
    (∫ x in (0 : ℝ)..2, periodicDensity h x) = 1 := by
  calc
    _ = ∫ x in (0 : ℝ)..2, h x := by
      apply intervalIntegral.integral_congr_uIoo
      intro x hx
      rw [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 2)] at hx
      exact periodicDensity_eq ⟨hx.1.le, hx.2⟩
    _ = 1 := hh.mass

theorem intervalIntegral_periodic_shift {f : ℝ → ℝ} (hf : Periodic f 2) (a : ℝ) :
    (∫ x in (0 : ℝ)..2, f (x + a)) = ∫ x in (0 : ℝ)..2, f x := by
  rw [intervalIntegral.integral_comp_add_right]
  convert hf.intervalIntegral_add_eq a 0 using 1 <;> congr 1 <;> ring

theorem periodicDensity_shift_mass {h : ℝ → ℝ} (hh : Admissible h) (a : ℝ) :
    (∫ x in (0 : ℝ)..2, periodicDensity h (x + a)) = 1 := by
  rw [intervalIntegral_periodic_shift (periodicDensity_periodic h), periodicDensity_mass hh]

theorem periodicDisagreement_intervalIntegrable {h : ℝ → ℝ} (hh : Admissible h)
    (s t a b : ℝ) :
    IntervalIntegrable
      (fun x => pairDisagreement (periodicDensity h (x + s)) (periodicDensity h (x + t)))
      volume a b := by
  wlog hab : a ≤ b
  · exact (this hh s t b a (le_of_not_ge hab)).symm
  have hm := periodicDensity_measurable hh
  apply intervalIntegrable_of_abs_le
    (((hm.comp (measurable_id.add_const s)).add (hm.comp (measurable_id.add_const t))).sub
      ((measurable_const.mul (hm.comp (measurable_id.add_const s))).mul
        (hm.comp (measurable_id.add_const t)))) hab (by norm_num : (0 : ℝ) ≤ 1)
  intro x _
  change |pairDisagreement (periodicDensity h (x + s)) (periodicDensity h (x + t))| ≤ 1
  rw [abs_of_nonneg (pairDisagreement_nonneg (periodicDensity_mem hh _) (periodicDensity_mem hh _))]
  exact pairDisagreement_le_one (periodicDensity_mem hh _) (periodicDensity_mem hh _)

theorem periodicDensity_shift_intervalIntegrable {h : ℝ → ℝ} (hh : Admissible h)
    (s a b : ℝ) :
    IntervalIntegrable (fun x => periodicDensity h (x + s)) volume a b := by
  convert (periodicDensity_intervalIntegrable hh (a + s) (b + s)).comp_add_right s using 1 <;> ring

theorem periodicDensity_product_intervalIntegrable {h : ℝ → ℝ} (hh : Admissible h)
    (s t a b : ℝ) :
    IntervalIntegrable (fun x => periodicDensity h (x + s) * periodicDensity h (x + t))
      volume a b := by
  wlog hab : a ≤ b
  · exact (this hh s t b a (le_of_not_ge hab)).symm
  have hm := periodicDensity_measurable hh
  apply intervalIntegrable_of_abs_le
    (f := fun x => periodicDensity h (x + s) * periodicDensity h (x + t))
    ((hm.comp (measurable_id.add_const s)).mul (hm.comp (measurable_id.add_const t)))
    hab (by norm_num : (0 : ℝ) ≤ 1)
  intro x _
  have hs := periodicDensity_mem hh (x + s)
  have ht := periodicDensity_mem hh (x + t)
  rw [abs_of_nonneg (mul_nonneg hs.1 ht.1)]
  nlinarith [ht.2, mul_nonneg (sub_nonneg.mpr hs.2) ht.1]

theorem periodicOverlap_integrand_intervalIntegrable {h : ℝ → ℝ} (hh : Admissible h)
    (s a b : ℝ) :
    IntervalIntegrable (fun x => periodicDensity h x * (1 - periodicDensity h (x + s)))
      volume a b := by
  have hp : IntervalIntegrable (fun x => periodicDensity h x * periodicDensity h (x + s))
      volume a b := by
    simpa only [add_zero] using periodicDensity_product_intervalIntegrable hh 0 s a b
  have hf := (periodicDensity_intervalIntegrable hh a b).sub hp
  simpa only [mul_sub, mul_one] using hf

theorem periodicOverlap_eq_one_sub {h : ℝ → ℝ} (hh : Admissible h) (s : ℝ) :
    periodicOverlap h s = 1 -
      ∫ x in (0 : ℝ)..2, periodicDensity h x * periodicDensity h (x + s) := by
  have hp : IntervalIntegrable (fun x => periodicDensity h x * periodicDensity h (x + s))
      volume 0 2 := by
    simpa only [add_zero] using periodicDensity_product_intervalIntegrable hh 0 s 0 2
  unfold periodicOverlap
  simp only [mul_sub, mul_one]
  rw [intervalIntegral.integral_sub (periodicDensity_intervalIntegrable hh 0 2) hp,
    periodicDensity_mass hh]

theorem periodicDisagreement_integral {h : ℝ → ℝ} (hh : Admissible h) (s : ℝ) :
    (∫ x in (0 : ℝ)..2,
      pairDisagreement (periodicDensity h x) (periodicDensity h (x + s))) =
        2 * periodicOverlap h s := by
  have hp : IntervalIntegrable (fun x => periodicDensity h x * periodicDensity h (x + s))
      volume 0 2 := by
    simpa only [add_zero] using periodicDensity_product_intervalIntegrable hh 0 s 0 2
  simp only [pairDisagreement, mul_assoc]
  rw [intervalIntegral.integral_sub
    ((periodicDensity_intervalIntegrable hh 0 2).add
      (periodicDensity_shift_intervalIntegrable hh s 0 2)) (hp.const_mul 2),
    intervalIntegral.integral_add (periodicDensity_intervalIntegrable hh 0 2)
      (periodicDensity_shift_intervalIntegrable hh s 0 2),
    intervalIntegral.integral_const_mul, periodicDensity_mass hh,
    periodicDensity_shift_mass hh, periodicOverlap_eq_one_sub hh]
  ring

theorem periodicDisagreement_shift_integral {h : ℝ → ℝ} (hh : Admissible h) (s t : ℝ) :
    (∫ x in (0 : ℝ)..2,
      pairDisagreement (periodicDensity h (x + s)) (periodicDensity h (x + t))) =
        2 * periodicOverlap h (t - s) := by
  have hp : Periodic (fun x =>
      pairDisagreement (periodicDensity h x) (periodicDensity h (x + (t - s)))) 2 := by
    intro x
    dsimp only
    rw [periodicDensity_periodic h x]
    have harg : x + 2 + (t - s) = (x + (t - s)) + 2 := by ring
    rw [harg, periodicDensity_periodic h]
  calc
    _ = ∫ x in (0 : ℝ)..2,
        pairDisagreement (periodicDensity h (x + s))
          (periodicDensity h ((x + s) + (t - s))) := by
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only
      have harg : (x + s) + (t - s) = x + t := by ring
      rw [harg]
    _ = ∫ x in (0 : ℝ)..2,
        pairDisagreement (periodicDensity h x) (periodicDensity h (x + (t - s))) :=
      intervalIntegral_periodic_shift hp s
    _ = _ := periodicDisagreement_integral hh (t - s)

theorem periodicOverlap_even {h : ℝ → ℝ} (hh : Admissible h) (s : ℝ) :
    periodicOverlap h (-s) = periodicOverlap h s := by
  have hshift := periodicDisagreement_shift_integral hh s 0
  have hbase := periodicDisagreement_integral hh s
  have heq : (fun x => pairDisagreement (periodicDensity h (x + s)) (periodicDensity h (x + 0))) =
      fun x => pairDisagreement (periodicDensity h x) (periodicDensity h (x + s)) := by
    funext x
    simp only [pairDisagreement, add_zero]
    ring
  rw [heq, hbase, zero_sub] at hshift
  linarith

theorem periodicOverlap_periodic (h : ℝ → ℝ) : Periodic (periodicOverlap h) 2 := by
  intro s
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [← add_assoc, periodicDensity_periodic h]

/-- This universal triangle row covers all eight nonperimeter native
families by substituting their two nonzero translated positions. -/
theorem periodicOverlap_triangle {h : ℝ → ℝ} (hh : Admissible h) (s t : ℝ) :
    periodicOverlap h t ≤ periodicOverlap h s + periodicOverlap h (t - s) := by
  have h0t := periodicDisagreement_intervalIntegrable hh 0 t 0 2
  have h0s := periodicDisagreement_intervalIntegrable hh 0 s 0 2
  have hst := periodicDisagreement_intervalIntegrable hh s t 0 2
  have hle := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 2) h0t (h0s.add hst)
    (fun x _ => pairDisagreement_triangle
      (periodicDensity_mem hh (x + 0)) (periodicDensity_mem hh (x + s))
      (periodicDensity_mem hh (x + t)))
  rw [intervalIntegral.integral_add h0s hst,
    periodicDisagreement_shift_integral hh 0 t,
    periodicDisagreement_shift_integral hh 0 s,
    periodicDisagreement_shift_integral hh s t] at hle
  simp only [sub_zero] at hle
  linarith

theorem periodicOverlap_perimeter {h : ℝ → ℝ} (hh : Admissible h) (s t : ℝ) :
    periodicOverlap h s + periodicOverlap h (t - s) + periodicOverlap h t ≤ 2 := by
  have h0s := periodicDisagreement_intervalIntegrable hh 0 s 0 2
  have hst := periodicDisagreement_intervalIntegrable hh s t 0 2
  have ht0 := periodicDisagreement_intervalIntegrable hh t 0 0 2
  have hle := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 2)
    ((h0s.add hst).add ht0) intervalIntegrable_const
    (fun x _ => pairDisagreement_perimeter
      (periodicDensity_mem hh (x + 0)) (periodicDensity_mem hh (x + s))
      (periodicDensity_mem hh (x + t)))
  rw [intervalIntegral.integral_add (h0s.add hst) ht0,
    intervalIntegral.integral_add h0s hst,
    periodicDisagreement_shift_integral hh 0 s,
    periodicDisagreement_shift_integral hh s t,
    periodicDisagreement_shift_integral hh t 0] at hle
  simp only [sub_zero, zero_sub, periodicOverlap_even hh] at hle
  norm_num at hle
  linarith

theorem periodicOverlap_mem {h : ℝ → ℝ} (hh : Admissible h) (s : ℝ) :
    periodicOverlap h s ∈ Icc (0 : ℝ) 1 := by
  constructor
  · apply intervalIntegral.integral_nonneg_of_forall (by norm_num : (0 : ℝ) ≤ 2)
    intro x
    exact mul_nonneg (periodicDensity_mem hh x).1
      (sub_nonneg.mpr (periodicDensity_mem hh (x + s)).2)
  · have hle := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 2)
      (periodicOverlap_integrand_intervalIntegrable hh s 0 2)
      (periodicDensity_intervalIntegrable hh 0 2) (fun x _ => ?_)
    · rw [periodicDensity_mass hh] at hle
      exact hle
    · apply mul_le_of_le_one_right (periodicDensity_mem hh x).1
      linarith [(periodicDensity_mem hh (x + s)).1]

theorem periodicOverlap_measurable {h : ℝ → ℝ} (hh : Admissible h) :
    Measurable (periodicOverlap h) := by
  have hm := periodicDensity_measurable hh
  have hj : Measurable (fun p : ℝ × ℝ =>
      periodicDensity h p.2 * (1 - periodicDensity h (p.2 + p.1))) :=
    (hm.comp measurable_snd).mul
      (measurable_const.sub (hm.comp (measurable_snd.add measurable_fst)))
  have hi : StronglyMeasurable (fun s => ∫ x in Ioc (0 : ℝ) 2,
      periodicDensity h x * (1 - periodicDensity h (x + s))) :=
    hj.stronglyMeasurable.integral_prod_right
  have heq : periodicOverlap h = fun s => ∫ x in Ioc (0 : ℝ) 2,
      periodicDensity h x * (1 - periodicDensity h (x + s)) := by
    funext s
    exact intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2)
  rw [heq]
  exact hi.measurable

theorem periodicOverlap_intervalIntegrable {h : ℝ → ℝ} (hh : Admissible h) (a b : ℝ) :
    IntervalIntegrable (periodicOverlap h) volume a b := by
  wlog hab : a ≤ b
  · exact (this hh b a (le_of_not_ge hab)).symm
  apply intervalIntegrable_of_abs_le (periodicOverlap_measurable hh) hab (by norm_num : (0 : ℝ) ≤ 1)
  intro x _
  rw [abs_of_nonneg (periodicOverlap_mem hh x).1]
  exact (periodicOverlap_mem hh x).2

/-- Splitting the wrapped correlation gives the two actual overlap pieces,
including the endpoints of the shift interval. -/
theorem periodicOverlap_eq_wrapped {h : ℝ → ℝ} (hh : Admissible h) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 2) :
    periodicOverlap h s = positiveOverlap h s + negativeOverlap h (2 - s) := by
  unfold periodicOverlap
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (periodicOverlap_integrand_intervalIntegrable hh s 0 (2 - s))
    (periodicOverlap_integrand_intervalIntegrable hh s (2 - s) 2)]
  congr 1
  · apply intervalIntegral.integral_congr_uIoo
    intro x hx
    rw [uIoo_of_le (by linarith [hs.2] : (0 : ℝ) ≤ 2 - s)] at hx
    dsimp only
    rw [periodicDensity_eq (show x ∈ Ico (0 : ℝ) 2 from
      ⟨hx.1.le, by linarith [hx.2, hs.1]⟩),
      periodicDensity_eq (show x + s ∈ Ico (0 : ℝ) 2 from
      ⟨by linarith [hx.1, hs.1], by linarith [hx.2]⟩)]
  · calc
      _ = ∫ x in (2 - s)..2, h x * (1 - h (x + s - 2)) := by
        apply intervalIntegral.integral_congr_uIoo
        intro x hx
        rw [uIoo_of_le (by linarith [hs.1] : 2 - s ≤ 2)] at hx
        dsimp only
        rw [periodicDensity_eq (show x ∈ Ico (0 : ℝ) 2 from
          ⟨by linarith [hx.1, hs.2], hx.2⟩),
          ← (periodicDensity_periodic h).sub_eq (x + s),
          periodicDensity_eq (show x + s - 2 ∈ Ico (0 : ℝ) 2 from
          ⟨by linarith [hx.1], by linarith [hx.2, hs.2]⟩)]
      _ = ∫ x in (0 : ℝ)..s, h (x + (2 - s)) * (1 - h x) := by
        have hc := intervalIntegral.integral_comp_add_right
          (fun x => h x * (1 - h (x + s - 2))) (a := (0 : ℝ)) (b := s) (2 - s)
        have hfun : (fun x => h (x + (2 - s)) * (1 - h (x + (2 - s) + s - 2))) =
            fun x => h (x + (2 - s)) * (1 - h x) := by
          funext x
          have harg : x + (2 - s) + s - 2 = x := by ring
          rw [harg]
        rw [hfun] at hc
        convert hc.symm using 1
        all_goals congr 1
        all_goals ring
      _ = negativeOverlap h (2 - s) := by
        unfold negativeOverlap
        congr 1; ring

/-- Every bounded measurable period-two weight has the same integral
against the wrapped correlation as against the physical difference law. -/
theorem periodicOverlap_pairing_eq_squarePairing
    {h W : ℝ → ℝ} {C : ℝ} (hh : Admissible h)
    (hW : Measurable W) (hbound : ∀ t, |W t| ≤ C) (hperiod : Periodic W 2) :
    (∫ t in (0 : ℝ)..2, W t * periodicOverlap h t) = squarePairing h W := by
  have hp := positiveOverlap_weighted_intervalIntegrable hh hW hbound
  have hn := negativeOverlap_weighted_intervalIntegrable hh hW hbound
  have hnref : IntervalIntegrable
      (fun t => W (-(2 - t)) * negativeOverlap h (2 - t)) volume 0 2 := by
    convert hn.symm.comp_sub_left 2 using 1 <;> norm_num
  have hrefeq : (fun t => W (-(2 - t)) * negativeOverlap h (2 - t)) =
      fun t => W t * negativeOverlap h (2 - t) := by
    funext t
    have harg : -(2 - t) = t - 2 := by ring
    rw [harg, hperiod.sub_eq]
  have href : IntervalIntegrable (fun t => W t * negativeOverlap h (2 - t)) volume 0 2 := by
    rwa [hrefeq] at hnref
  have hreflection : (∫ t in (0 : ℝ)..2, W t * negativeOverlap h (2 - t)) =
      ∫ t in (0 : ℝ)..2, W (-t) * negativeOverlap h t := by
    rw [← hrefeq]
    have hc := intervalIntegral.integral_comp_sub_left
      (fun t => W (-t) * negativeOverlap h t) (a := (0 : ℝ)) (b := 2) 2
    convert hc using 1
    all_goals norm_num
  calc
    _ = ∫ t in (0 : ℝ)..2,
        W t * positiveOverlap h t + W t * negativeOverlap h (2 - t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
      dsimp only
      rw [periodicOverlap_eq_wrapped hh ht, mul_add]
    _ = (∫ t in (0 : ℝ)..2, W t * positiveOverlap h t) +
        ∫ t in (0 : ℝ)..2, W t * negativeOverlap h (2 - t) :=
      intervalIntegral.integral_add hp href
    _ = signedOverlapPairing h W := by
      rw [hreflection]
      exact (intervalIntegral.integral_add hp hn).symm
    _ = _ := (squarePairing_eq_signedOverlapPairing hh hW hbound).symm

theorem periodicOverlap_dilate_intervalIntegrable {h : ℝ → ℝ} (hh : Admissible h)
    (k a b : ℝ) : IntervalIntegrable (fun x => periodicOverlap h (k * x)) volume a b := by
  wlog hab : a ≤ b
  · exact (this hh k b a (le_of_not_ge hab)).symm
  apply intervalIntegrable_of_abs_le
    (f := fun x => periodicOverlap h (k * x))
    ((periodicOverlap_measurable hh).comp (measurable_const.mul measurable_id))
    hab (by norm_num : (0 : ℝ) ≤ 1)
  intro x _
  rw [abs_of_nonneg (periodicOverlap_mem hh (k * x)).1]
  exact (periodicOverlap_mem hh (k * x)).2

/-- The unnormalized averaged triangle row, before exact grid compilation. -/
theorem periodicOverlap_averaged_triangle {h : ℝ → ℝ} (hh : Admissible h)
    (r k : ℝ) {a b : ℝ} (hab : a ≤ b) :
    (∫ x in a..b, periodicOverlap h (k * x)) -
      (∫ x in a..b, periodicOverlap h (r * x)) -
      (∫ x in a..b, periodicOverlap h ((k - r) * x)) ≤ 0 := by
  have hr := periodicOverlap_dilate_intervalIntegrable hh r a b
  have hk := periodicOverlap_dilate_intervalIntegrable hh k a b
  have hkr := periodicOverlap_dilate_intervalIntegrable hh (k - r) a b
  have hle := intervalIntegral.integral_mono_on hab hk (hr.add hkr) (fun x _ => ?_)
  · rw [intervalIntegral.integral_add hr hkr] at hle
    linarith
  · have ht := periodicOverlap_triangle hh (r * x) (k * x)
    have harg : k * x - r * x = (k - r) * x := by ring
    rwa [harg] at ht

/-- The unnormalized averaged perimeter row has right-hand side exactly
twice the averaging interval's length. -/
theorem periodicOverlap_averaged_perimeter {h : ℝ → ℝ} (hh : Admissible h)
    (r k : ℝ) {a b : ℝ} (hab : a ≤ b) :
    (∫ x in a..b, periodicOverlap h (r * x)) +
      (∫ x in a..b, periodicOverlap h ((k - r) * x)) +
      (∫ x in a..b, periodicOverlap h (k * x)) ≤ 2 * (b - a) := by
  have hr := periodicOverlap_dilate_intervalIntegrable hh r a b
  have hk := periodicOverlap_dilate_intervalIntegrable hh k a b
  have hkr := periodicOverlap_dilate_intervalIntegrable hh (k - r) a b
  have hle := intervalIntegral.integral_mono_on hab ((hr.add hkr).add hk)
    (intervalIntegrable_const (c := (2 : ℝ))) (fun x _ => ?_)
  · rw [intervalIntegral.integral_add (hr.add hkr) hk,
      intervalIntegral.integral_add hr hkr, intervalIntegral.integral_const] at hle
    simpa only [smul_eq_mul, mul_comm] using hle
  · have ht := periodicOverlap_perimeter hh (r * x) (k * x)
    have harg : k * x - r * x = (k - r) * x := by ring
    rwa [harg] at ht

theorem periodicOverlap_weighted_intervalIntegrable
    {h W : ℝ → ℝ} {C : ℝ} (hh : Admissible h)
    (hW : Measurable W) (hbound : ∀ t, |W t| ≤ C) (a b : ℝ) :
    IntervalIntegrable (fun t => W t * periodicOverlap h t) volume a b := by
  wlog hab : a ≤ b
  · exact (this hh hW hbound b a (le_of_not_ge hab)).symm
  have hC : 0 ≤ C := (abs_nonneg (W 0)).trans (hbound 0)
  apply intervalIntegrable_of_abs_le (hW.mul (periodicOverlap_measurable hh)) hab hC
  intro t _
  change |W t * periodicOverlap h t| ≤ C
  rw [abs_mul, abs_of_nonneg (periodicOverlap_mem hh t).1]
  exact (mul_le_mul_of_nonneg_right (hbound t) (periodicOverlap_mem hh t).1).trans
    (by nlinarith [(periodicOverlap_mem hh t).2])

@[expose] def symmetrizeWeight (W : ℝ → ℝ) (t : ℝ) : ℝ := (W t + W (-t)) / 2

theorem symmetrizeWeight_even (W : ℝ → ℝ) (t : ℝ) :
    symmetrizeWeight W (-t) = symmetrizeWeight W t := by
  simp only [symmetrizeWeight, neg_neg, add_comm]

theorem symmetrizeWeight_measurable {W : ℝ → ℝ} (hW : Measurable W) :
    Measurable (symmetrizeWeight W) :=
  (hW.add (hW.comp measurable_neg)).div_const 2

theorem symmetrizeWeight_bound {W : ℝ → ℝ} {C : ℝ} (hbound : ∀ t, |W t| ≤ C) (t : ℝ) :
    |symmetrizeWeight W t| ≤ C := by
  unfold symmetrizeWeight
  rw [abs_div]
  norm_num
  have hs := abs_add_le (W t) (W (-t))
  linarith [hbound t, hbound (-t)]

theorem symmetrizeWeight_periodic {W : ℝ → ℝ} (hW : Periodic W 2) :
    Periodic (symmetrizeWeight W) 2 := by
  intro t
  unfold symmetrizeWeight
  rw [hW t]
  have harg : -(t + 2) = -t - 2 := by ring
  rw [harg, hW.sub_eq]

theorem periodicOverlap_reflect_weight {h W : ℝ → ℝ} (hh : Admissible h)
    (hW : Periodic W 2) :
    (∫ t in (0 : ℝ)..2, W (-t) * periodicOverlap h t) =
      ∫ t in (0 : ℝ)..2, W t * periodicOverlap h t := by
  have heq : (fun t => W (-(2 - t)) * periodicOverlap h (2 - t)) =
      fun t => W t * periodicOverlap h t := by
    funext t
    have hwarg : -(2 - t) = t - 2 := by ring
    have hqarg : 2 - t = -t + 2 := by ring
    rw [hwarg, hW.sub_eq, hqarg, periodicOverlap_periodic h,
      periodicOverlap_even hh]
  have hc := intervalIntegral.integral_comp_sub_left
    (fun t => W (-t) * periodicOverlap h t) (a := (0 : ℝ)) (b := 2) 2
  rw [heq] at hc
  convert hc.symm using 1
  all_goals norm_num

/-- Symmetrizing a periodic test changes no physical expectation. This is
the exact reversal symmetrization in the native step compiler. -/
theorem squarePairing_symmetrizeWeight
    {h W : ℝ → ℝ} {C : ℝ} (hh : Admissible h)
    (hW : Measurable W) (hbound : ∀ t, |W t| ≤ C) (hperiod : Periodic W 2) :
    squarePairing h (symmetrizeWeight W) = squarePairing h W := by
  rw [← periodicOverlap_pairing_eq_squarePairing hh
    (symmetrizeWeight_measurable hW) (symmetrizeWeight_bound hbound)
    (symmetrizeWeight_periodic hperiod),
    ← periodicOverlap_pairing_eq_squarePairing hh hW hbound hperiod]
  have hi := periodicOverlap_weighted_intervalIntegrable hh hW hbound 0 2
  have hin := periodicOverlap_weighted_intervalIntegrable (W := fun t => W (-t)) hh (hW.comp measurable_neg)
    (fun t => hbound (-t)) 0 2
  have heq : (fun t => symmetrizeWeight W t * periodicOverlap h t) =
      fun t => (2 : ℝ)⁻¹ * (W t * periodicOverlap h t + W (-t) * periodicOverlap h t) := by
    funext t
    unfold symmetrizeWeight
    ring
  rw [heq, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hi hin, periodicOverlap_reflect_weight hh hperiod]
  ring

theorem quartetFunctional_symmetrizeWeight
    {h W : ℝ → ℝ} {C : ℝ} (hh : Admissible h)
    (hW : Measurable W) (hbound : ∀ t, |W t| ≤ C) (hperiod : Periodic W 2) :
    quartetFunctional h (symmetrizeWeight W) = squarePairing h W := by
  rw [← squarePairing_eq_quartetFunctional hh (symmetrizeWeight_measurable hW)
    (symmetrizeWeight_bound hbound) (symmetrizeWeight_even W),
    squarePairing_symmetrizeWeight hh hW hbound hperiod]

end
end
end ErdosOverlap
