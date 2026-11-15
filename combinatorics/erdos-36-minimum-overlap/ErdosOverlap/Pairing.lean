/-
Copyright (c) 2026. Released under the BSD-3-Clause license.
-/
module

public import ErdosOverlap.Fourier
public import ErdosOverlap.KernelDual
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Support and Fubini identities for physical overlap expectations

Both complementary densities are extended by zero outside `[0,2]`.
The whole-line correlation is related to the interval-defined signed
overlaps before its test-function pairing is transformed by Fubini.
-/

namespace ErdosOverlap

open MeasureTheory Set
open scoped Interval Convolution

public section
noncomputable section

@[expose] def supportedDensity (h : ℝ → ℝ) : ℝ → ℝ :=
  (Icc (0 : ℝ) 2).indicator h

@[expose] def supportedComplement (h : ℝ → ℝ) : ℝ → ℝ :=
  (Icc (0 : ℝ) 2).indicator (fun x => 1 - h x)

@[expose] def wholeOverlap (h : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x : ℝ, supportedDensity h x * supportedComplement h (x + t)

theorem supportedDensity_measurable {h : ℝ → ℝ} (hh : Admissible h) :
    Measurable (supportedDensity h) := hh.measurable.indicator measurableSet_Icc

theorem supportedComplement_measurable {h : ℝ → ℝ} (hh : Admissible h) :
    Measurable (supportedComplement h) :=
  (measurable_const.sub hh.measurable).indicator measurableSet_Icc

theorem supportedDensity_integrable {h : ℝ → ℝ} (hh : Admissible h) :
    Integrable (supportedDensity h) := by
  apply IntegrableOn.integrable_indicator _ measurableSet_Icc
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 2)).mp
    (hh.intervalIntegrable (by norm_num) (by norm_num) (by norm_num))

theorem supportedComplement_integrable {h : ℝ → ℝ} (hh : Admissible h) :
    Integrable (supportedComplement h) := by
  apply IntegrableOn.integrable_indicator _ measurableSet_Icc
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 2)).mp
    hh.complement_intervalIntegrable

/-- Exact support intersection for a nonnegative shift. -/
theorem positive_correlation_integrand (h : ℝ → ℝ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 2) :
    (fun x => supportedDensity h x * supportedComplement h (x + t)) =
      (Icc (0 : ℝ) (2 - t)).indicator (fun x => h x * (1 - h (x + t))) := by
  funext x
  by_cases hx : x ∈ Icc (0 : ℝ) (2 - t)
  · have hx₀ : x ∈ Icc (0 : ℝ) 2 := ⟨hx.1, by linarith [hx.2, ht.1]⟩
    have hxt : x + t ∈ Icc (0 : ℝ) 2 :=
      ⟨by linarith [hx.1, ht.1], by linarith [hx.2]⟩
    simp [supportedDensity, supportedComplement, hx, hx₀, hxt]
  · by_cases hx₀ : x ∈ Icc (0 : ℝ) 2
    · have hxt : x + t ∉ Icc (0 : ℝ) 2 := by
        intro hxt
        exact hx ⟨hx₀.1, by linarith [hxt.2]⟩
      simp [supportedDensity, supportedComplement, hx, hx₀, hxt]
    · simp [supportedDensity, supportedComplement, hx, hx₀]

theorem wholeOverlap_eq_positive (h : ℝ → ℝ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 2) : wholeOverlap h t = positiveOverlap h t := by
  unfold wholeOverlap positiveOverlap
  rw [positive_correlation_integrand h ht, integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by linarith [ht.2])]

/-- Exact support intersection for a nonpositive shift. -/
theorem negative_correlation_integrand (h : ℝ → ℝ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 2) :
    (fun x => supportedDensity h x * supportedComplement h (x - t)) =
      (Icc t 2).indicator (fun x => h x * (1 - h (x - t))) := by
  funext x
  by_cases hx : x ∈ Icc t 2
  · have hx₀ : x ∈ Icc (0 : ℝ) 2 := ⟨by linarith [hx.1, ht.1], hx.2⟩
    have hxt : x - t ∈ Icc (0 : ℝ) 2 :=
      ⟨by linarith [hx.1], by linarith [hx.2, ht.1]⟩
    simp [supportedDensity, supportedComplement, hx, hx₀, hxt]
  · by_cases hx₀ : x ∈ Icc (0 : ℝ) 2
    · have hxt : x - t ∉ Icc (0 : ℝ) 2 := by
        intro hxt
        exact hx ⟨by linarith [hxt.1], hx₀.2⟩
      simp [supportedDensity, supportedComplement, hx, hx₀, hxt]
    · simp [supportedDensity, supportedComplement, hx, hx₀]

theorem wholeOverlap_neg_eq_negative (h : ℝ → ℝ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 2) : wholeOverlap h (-t) = negativeOverlap h t := by
  unfold wholeOverlap negativeOverlap
  simp only [← sub_eq_add_neg]
  rw [negative_correlation_integrand h ht, integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht.2]
  have hchange := intervalIntegral.integral_comp_add_right
    (fun x => h x * (1 - h (x - t))) (a := (0 : ℝ)) (b := 2 - t) t
  simpa only [zero_add, sub_add_cancel, add_sub_cancel_right] using hchange.symm

theorem wholeOverlap_eq_zero_off_support (h : ℝ → ℝ) {t : ℝ}
    (ht : t ∉ Icc (-2 : ℝ) 2) : wholeOverlap h t = 0 := by
  unfold wholeOverlap
  have hzero (x : ℝ) : supportedDensity h x * supportedComplement h (x + t) = 0 := by
    by_cases hx : x ∈ Icc (0 : ℝ) 2
    · have hxt : x + t ∉ Icc (0 : ℝ) 2 := by
        intro hxt
        exact ht ⟨by linarith [hxt.1, hx.2], by linarith [hxt.2, hx.1]⟩
      simp [supportedComplement, hxt]
    · simp [supportedDensity, hx]
  simp only [hzero, integral_zero]

/-- The whole overlap is an ordinary convolution after reflecting the first
density. Both densities are zero outside their support. -/
theorem wholeOverlap_eq_convolution (h : ℝ → ℝ) (t : ℝ) :
    wholeOverlap h t =
      ((fun x => supportedDensity h (-x)) ⋆[ContinuousLinearMap.mul ℝ ℝ]
        supportedComplement h) t := by
  change (∫ x : ℝ, supportedDensity h x * supportedComplement h (x + t)) =
    ∫ x : ℝ, supportedDensity h (-x) * supportedComplement h (t - x)
  simpa only [sub_eq_add_neg, add_comm] using
    (integral_neg_eq_self
      (fun x => supportedDensity h x * supportedComplement h (x + t)) volume).symm

theorem wholeOverlap_integrable {h : ℝ → ℝ} (hh : Admissible h) :
    Integrable (wholeOverlap h) := by
  have hi := (supportedDensity_integrable hh).comp_neg.integrable_convolution
    (ContinuousLinearMap.mul ℝ ℝ) (supportedComplement_integrable hh)
  exact hi.congr (Filter.Eventually.of_forall (fun t => (wholeOverlap_eq_convolution h t).symm))

/-- Fubini and translation invariance turn a bounded measurable whole-line
test pairing into the actual two-density expectation. -/
theorem wholeOverlap_pairing_eq_supported_pairing
    {h K : ℝ → ℝ} {C : ℝ} (hh : Admissible h)
    (hK : Measurable K) (hbound : ∀ t, |K t| ≤ C) :
    (∫ t : ℝ, K t * wholeOverlap h t) =
      ∫ x : ℝ, ∫ y : ℝ,
        supportedDensity h x * supportedComplement h y * K (y - x) := by
  have hbase : Integrable
      (fun p : ℝ × ℝ => supportedDensity h (-p.2) * supportedComplement h (p.1 - p.2))
      (volume.prod volume) := by
    exact (supportedDensity_integrable hh).comp_neg.convolution_integrand
      (ContinuousLinearMap.mul ℝ ℝ) (supportedComplement_integrable hh)
  have hweighted : Integrable
      (fun p : ℝ × ℝ => K p.1 *
        (supportedDensity h (-p.2) * supportedComplement h (p.1 - p.2)))
      (volume.prod volume) := by
    apply hbase.bdd_mul (hK.comp measurable_fst).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun p => by
      simpa only [Real.norm_eq_abs, Function.comp_apply] using hbound p.1)
  calc
    _ = ∫ t : ℝ, ∫ x : ℝ,
        K t * (supportedDensity h (-x) * supportedComplement h (t - x)) := by
      apply integral_congr_ae
      filter_upwards with t
      rw [wholeOverlap_eq_convolution]
      change K t * (∫ x : ℝ,
        supportedDensity h (-x) * supportedComplement h (t - x)) = _
      exact (integral_const_mul _ _).symm
    _ = ∫ x : ℝ, ∫ t : ℝ,
        K t * (supportedDensity h (-x) * supportedComplement h (t - x)) :=
      integral_integral_swap hweighted
    _ = ∫ x : ℝ, ∫ y : ℝ,
        K (y + x) * (supportedDensity h (-x) * supportedComplement h y) := by
      apply integral_congr_ae
      filter_upwards with x
      simpa only [add_sub_cancel_right] using
        (integral_add_right_eq_self
          (fun t => K t * (supportedDensity h (-x) * supportedComplement h (t - x))) x).symm
    _ = ∫ x : ℝ, ∫ y : ℝ,
        K (y - x) * (supportedDensity h x * supportedComplement h y) := by
      simpa only [sub_neg_eq_add] using
        (integral_neg_eq_self
          (fun x => ∫ y : ℝ, K (y - x) *
            (supportedDensity h x * supportedComplement h y)) volume)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      apply integral_congr_ae
      filter_upwards with y
      ring

/-- Removing the support indicators gives the literal interval-square
expectation used in the Fourier identities. -/
theorem supported_pairing_eq_squarePairing (h K : ℝ → ℝ) :
    (∫ x : ℝ, ∫ y : ℝ,
      supportedDensity h x * supportedComplement h y * K (y - x)) = squarePairing h K := by
  have hout : ∀ x, x ∉ Icc (0 : ℝ) 2 →
      (∫ y : ℝ, supportedDensity h x * supportedComplement h y * K (y - x)) = 0 := by
    intro x hx
    simp [supportedDensity, hx]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hout,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2)]
  unfold squarePairing
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x ∈ Icc (0 : ℝ) 2 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using hx
  have hfun : (fun y => supportedDensity h x * supportedComplement h y * K (y - x)) =
      (Icc (0 : ℝ) 2).indicator (fun y => h x * (1 - h y) * K (y - x)) := by
    funext y
    by_cases hy : y ∈ Icc (0 : ℝ) 2
    · simp [supportedDensity, supportedComplement, hx', hy]
    · simp [supportedDensity, supportedComplement, hx', hy]
  dsimp only
  rw [hfun, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2)]

theorem wholeOverlap_pairing_eq_squarePairing
    {h K : ℝ → ℝ} {C : ℝ} (hh : Admissible h)
    (hK : Measurable K) (hbound : ∀ t, |K t| ≤ C) :
    (∫ t : ℝ, K t * wholeOverlap h t) = squarePairing h K := by
  rw [wholeOverlap_pairing_eq_supported_pairing hh hK hbound,
    supported_pairing_eq_squarePairing]

@[expose] def signedOverlapIntegrand (h K : ℝ → ℝ) (t : ℝ) : ℝ :=
  K t * positiveOverlap h t + K (-t) * negativeOverlap h t

@[expose] def signedOverlapPairing (h K : ℝ → ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..2, signedOverlapIntegrand h K t

theorem wholeOverlap_weighted_integrable
    {h K : ℝ → ℝ} {C : ℝ} (hh : Admissible h)
    (hK : Measurable K) (hbound : ∀ t, |K t| ≤ C) :
    Integrable (fun t => K t * wholeOverlap h t) := by
  apply (wholeOverlap_integrable hh).bdd_mul hK.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => by
    simpa only [Real.norm_eq_abs] using hbound t)

theorem positiveOverlap_weighted_intervalIntegrable
    {h K : ℝ → ℝ} {C : ℝ} (hh : Admissible h)
    (hK : Measurable K) (hbound : ∀ t, |K t| ≤ C) :
    IntervalIntegrable (fun t => K t * positiveOverlap h t) volume 0 2 := by
  apply (wholeOverlap_weighted_integrable hh hK hbound).intervalIntegrable.congr_uIoo
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 2 := by
    rw [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
    exact ⟨ht.1.le, ht.2.le⟩
  dsimp only
  rw [wholeOverlap_eq_positive h ht']

theorem negativeOverlap_weighted_intervalIntegrable
    {h K : ℝ → ℝ} {C : ℝ} (hh : Admissible h)
    (hK : Measurable K) (hbound : ∀ t, |K t| ≤ C) :
    IntervalIntegrable (fun t => K (-t) * negativeOverlap h t) volume 0 2 := by
  apply (wholeOverlap_weighted_integrable hh hK hbound).comp_neg.intervalIntegrable.congr_uIoo
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 2 := by
    rw [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
    exact ⟨ht.1.le, ht.2.le⟩
  dsimp only
  rw [wholeOverlap_neg_eq_negative h ht']

theorem signedOverlapIntegrand_intervalIntegrable
    {h K : ℝ → ℝ} {C : ℝ} (hh : Admissible h)
    (hK : Measurable K) (hbound : ∀ t, |K t| ≤ C) :
    IntervalIntegrable (signedOverlapIntegrand h K) volume 0 2 :=
  (positiveOverlap_weighted_intervalIntegrable hh hK hbound).add
    (negativeOverlap_weighted_intervalIntegrable hh hK hbound)

/-- The negative half of the whole-line correlation is precisely the
negative physical overlap. No symmetry of the density is assumed. -/
theorem wholeOverlap_pairing_eq_signedOverlapPairing
    {h K : ℝ → ℝ} {C : ℝ} (hh : Admissible h)
    (hK : Measurable K) (hbound : ∀ t, |K t| ≤ C) :
    (∫ t : ℝ, K t * wholeOverlap h t) = signedOverlapPairing h K := by
  have hfull := wholeOverlap_weighted_integrable hh hK hbound
  have hout : ∀ t, t ∉ Icc (-2 : ℝ) 2 → K t * wholeOverlap h t = 0 := by
    intro t ht
    rw [wholeOverlap_eq_zero_off_support h ht, mul_zero]
  have hnegative : (∫ t in (-2 : ℝ)..0, K t * wholeOverlap h t) =
      ∫ t in (0 : ℝ)..2, K (-t) * negativeOverlap h t := by
    calc
      _ = ∫ t in (0 : ℝ)..2, K (-t) * wholeOverlap h (-t) := by
        simpa only [zero_sub, sub_zero] using
          (intervalIntegral.integral_comp_sub_left
            (fun t => K t * wholeOverlap h t) (a := 0) (b := 2) 0).symm
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht' : t ∈ Icc (0 : ℝ) 2 := by
          simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
        dsimp only
        rw [wholeOverlap_neg_eq_negative h ht']
  have hpositive : (∫ t in (0 : ℝ)..2, K t * wholeOverlap h t) =
      ∫ t in (0 : ℝ)..2, K t * positiveOverlap h t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 2 := by
      simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht
    dsimp only
    rw [wholeOverlap_eq_positive h ht']
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hout,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-2 : ℝ) ≤ 2),
    ← intervalIntegral.integral_add_adjacent_intervals
      (hfull.intervalIntegrable (a := -2) (b := 0))
      (hfull.intervalIntegrable (a := 0) (b := 2)),
    hnegative, hpositive]
  unfold signedOverlapPairing signedOverlapIntegrand
  rw [intervalIntegral.integral_add
    (positiveOverlap_weighted_intervalIntegrable hh hK hbound)
    (negativeOverlap_weighted_intervalIntegrable hh hK hbound)]
  exact add_comm _ _

theorem squarePairing_eq_signedOverlapPairing
    {h K : ℝ → ℝ} {C : ℝ} (hh : Admissible h)
    (hK : Measurable K) (hbound : ∀ t, |K t| ≤ C) :
    squarePairing h K = signedOverlapPairing h K := by
  rw [← wholeOverlap_pairing_eq_squarePairing hh hK hbound,
    wholeOverlap_pairing_eq_signedOverlapPairing hh hK hbound]

/-- Reflection folds an integral on `[0,2]` into the paired integral on
`[0,1]` used by the four-overlap duality theorem. -/
theorem integral_fold_at_one {F : ℝ → ℝ}
    (hF : IntervalIntegrable F volume 0 2) :
    (∫ t in (0 : ℝ)..2, F t) = ∫ t in (0 : ℝ)..1, F t + F (2 - t) := by
  have h01 : IntervalIntegrable F volume 0 1 := hF.mono_set (by
    simp only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1),
      uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)]
    intro t ht
    exact ⟨ht.1, by linarith [ht.2]⟩)
  have h12 : IntervalIntegrable F volume 1 2 := hF.mono_set (by
    simp only [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2),
      uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)]
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩)
  have hreflect : IntervalIntegrable (fun t => F (2 - t)) volume 0 1 := by
    convert h12.symm.comp_sub_left 2 using 1 <;> norm_num
  rw [← intervalIntegral.integral_add_adjacent_intervals h01 h12,
    intervalIntegral.integral_add h01 hreflect,
    intervalIntegral.integral_comp_sub_left]
  norm_num

/-- For an even bounded measurable kernel the physical quartet functional
is exactly the expectation over two complementary densities. -/
theorem squarePairing_eq_quartetFunctional
    {h K : ℝ → ℝ} {C : ℝ} (hh : Admissible h)
    (hK : Measurable K) (hbound : ∀ t, |K t| ≤ C)
    (heven : ∀ t, K (-t) = K t) :
    squarePairing h K = quartetFunctional h K := by
  have heq : signedOverlapIntegrand h K =
      fun t => K t * (positiveOverlap h t + negativeOverlap h t) := by
    funext t
    simp only [signedOverlapIntegrand, heven, mul_add]
  rw [squarePairing_eq_signedOverlapPairing hh hK hbound]
  unfold signedOverlapPairing
  rw [heq]
  have hF := signedOverlapIntegrand_intervalIntegrable hh hK hbound
  rw [heq] at hF
  exact integral_fold_at_one hF

theorem squarePairing_congr_on {h K J : ℝ → ℝ}
    (hKJ : EqOn K J (Icc (-2 : ℝ) 2)) : squarePairing h K = squarePairing h J := by
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at hx
  apply intervalIntegral.integral_congr
  intro y hy
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at hy
  dsimp only
  rw [hKJ ⟨by linarith [hy.1, hx.2], by linarith [hy.2, hx.1]⟩]

theorem signedOverlapPairing_congr_on {h K J : ℝ → ℝ}
    (hKJ : EqOn K J (Icc (-2 : ℝ) 2)) :
    signedOverlapPairing h K = signedOverlapPairing h J := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
  dsimp only [signedOverlapIntegrand]
  rw [hKJ ⟨by linarith [ht.1], ht.2⟩,
    hKJ ⟨by linarith [ht.2], by linarith [ht.1]⟩]

theorem quartetFunctional_congr_on {h K J : ℝ → ℝ}
    (hKJ : EqOn K J (Icc (0 : ℝ) 2)) :
    quartetFunctional h K = quartetFunctional h J := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
  dsimp only [quartetIntegrand]
  rw [hKJ ⟨ht.1, by linarith [ht.2]⟩,
    hKJ ⟨by linarith [ht.2], by linarith [ht.1]⟩]

/-- The support reduction permits kernels, such as polynomials, which are
bounded only on the actual difference support. -/
theorem squarePairing_eq_signedOverlapPairing_of_boundedOn
    {h K : ℝ → ℝ} {C : ℝ} (hh : Admissible h)
    (hK : Measurable K) (hbound : ∀ t ∈ Icc (-2 : ℝ) 2, |K t| ≤ C) :
    squarePairing h K = signedOverlapPairing h K := by
  let J := (Icc (-2 : ℝ) 2).indicator K
  have heq : EqOn J K (Icc (-2 : ℝ) 2) := by
    intro t ht
    exact indicator_of_mem ht K
  have hC : 0 ≤ C := (abs_nonneg (K 0)).trans (hbound 0 (by constructor <;> norm_num))
  have hb : ∀ t, |J t| ≤ C := by
    intro t
    by_cases ht : t ∈ Icc (-2 : ℝ) 2
    · rw [heq ht]
      exact hbound t ht
    · simp only [J, indicator_of_notMem ht, abs_zero]
      exact hC
  calc
    _ = squarePairing h J := (squarePairing_congr_on heq).symm
    _ = signedOverlapPairing h J :=
      squarePairing_eq_signedOverlapPairing hh (hK.indicator measurableSet_Icc) hb
    _ = _ := signedOverlapPairing_congr_on heq

theorem squarePairing_eq_quartetFunctional_of_boundedOn
    {h K : ℝ → ℝ} {C : ℝ} (hh : Admissible h)
    (hK : Measurable K) (hbound : ∀ t ∈ Icc (-2 : ℝ) 2, |K t| ≤ C)
    (heven : ∀ t, K (-t) = K t) :
    squarePairing h K = quartetFunctional h K := by
  let J := (Icc (-2 : ℝ) 2).indicator K
  have heq : EqOn J K (Icc (-2 : ℝ) 2) := by
    intro t ht
    exact indicator_of_mem ht K
  have hC : 0 ≤ C := (abs_nonneg (K 0)).trans (hbound 0 (by constructor <;> norm_num))
  have hb : ∀ t, |J t| ≤ C := by
    intro t
    by_cases ht : t ∈ Icc (-2 : ℝ) 2
    · rw [heq ht]
      exact hbound t ht
    · simp only [J, indicator_of_notMem ht, abs_zero]
      exact hC
  have hJeven : ∀ t, J (-t) = J t := by
    intro t
    have hneg : -t ∈ Icc (-2 : ℝ) 2 ↔ t ∈ Icc (-2 : ℝ) 2 := by
      constructor <;> intro ht <;> constructor <;> linarith [ht.1, ht.2]
    by_cases ht : t ∈ Icc (-2 : ℝ) 2
    · simp only [J, indicator_of_mem ht, indicator_of_mem (hneg.mpr ht), heven]
    · have hn : -t ∉ Icc (-2 : ℝ) 2 := fun hn => ht (hneg.mp hn)
      simp only [J, indicator_of_notMem ht, indicator_of_notMem hn]
  calc
    _ = squarePairing h J := (squarePairing_congr_on heq).symm
    _ = quartetFunctional h J :=
      squarePairing_eq_quartetFunctional hh (hK.indicator measurableSet_Icc) hb hJeven
    _ = _ := quartetFunctional_congr_on (fun t ht => heq ⟨by linarith [ht.1], ht.2⟩)

theorem squarePairing_eq_signedOverlapPairing_of_continuous
    {h K : ℝ → ℝ} (hh : Admissible h) (hK : Continuous K) :
    squarePairing h K = signedOverlapPairing h K := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (-2 : ℝ) 2)).exists_bound_of_continuousOn hK.continuousOn
  apply squarePairing_eq_signedOverlapPairing_of_boundedOn (C := C) hh hK.measurable
  simpa only [Real.norm_eq_abs] using hC

theorem squarePairing_eq_quartetFunctional_of_continuous
    {h K : ℝ → ℝ} (hh : Admissible h) (hK : Continuous K)
    (heven : ∀ t, K (-t) = K t) :
    squarePairing h K = quartetFunctional h K := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (-2 : ℝ) 2)).exists_bound_of_continuousOn hK.continuousOn
  apply squarePairing_eq_quartetFunctional_of_boundedOn (C := C) hh hK.measurable _ heven
  simpa only [Real.norm_eq_abs] using hC

end
end
end ErdosOverlap
