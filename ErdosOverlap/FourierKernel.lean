/-
Copyright (c) 2026. Released under the BSD-3-Clause license.
-/
module

public import ErdosOverlap.Pairing
public import ErdosOverlap.Moment

/-!
# Fourier and polynomial rows for the actual physical kernel functional

This module discharges the cosine and moment expectations directly from
admissibility. The frequency convention is `cos (ξ*t)`, and the mean is
the already formalized `profileMean (overlapProfile h)`.
-/

namespace ErdosOverlap

open MeasureTheory Set
open scoped Interval

public section
noncomputable section

theorem quartetFunctional_cos_identity {h : ℝ → ℝ} (hh : Admissible h) (ξ : ℝ) :
    quartetFunctional h (fun t => Real.cos (ξ * t)) =
      Real.sinc ξ ^ 2 - (contrastCos h ξ ^ 2 + contrastSin h ξ ^ 2) / 4 := by
  rw [← squarePairing_eq_quartetFunctional_of_continuous (K := fun t => Real.cos (ξ * t)) hh
    (Real.continuous_cos.comp (continuous_const.mul continuous_id))
    (fun t => by simp only [mul_neg, Real.cos_neg])]
  exact squarePairing_cos_identity hh ξ

theorem quartetFunctional_cos_le_sinc_sq {h : ℝ → ℝ} (hh : Admissible h) (ξ : ℝ) :
    quartetFunctional h (fun t => Real.cos (ξ * t)) ≤ Real.sinc ξ ^ 2 := by
  rw [quartetFunctional_cos_identity hh ξ]
  nlinarith [sq_nonneg (contrastCos h ξ), sq_nonneg (contrastSin h ξ)]

theorem quartetFunctional_nonpositive_cosine_row {h : ℝ → ℝ} (hh : Admissible h)
    (ξ : ℝ) {z : ℝ} (hz : z ≤ 0) :
    z * Real.sinc ξ ^ 2 ≤ z * quartetFunctional h (fun t => Real.cos (ξ * t)) :=
  mul_le_mul_of_nonpos_left (quartetFunctional_cos_le_sinc_sq hh ξ) hz

theorem Admissible.complement_mass {h : ℝ → ℝ} (hh : Admissible h) :
    (∫ x in (0 : ℝ)..2, 1 - h x) = 1 := by
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    (hh.intervalIntegrable (by norm_num) (by norm_num) (by norm_num)), hh.mass]
  norm_num

theorem Admissible.complement {h : ℝ → ℝ} (hh : Admissible h) :
    Admissible (fun x => 1 - h x) where
  measurable := measurable_const.sub hh.measurable
  nonneg := fun x hx => sub_nonneg.mpr (hh.le_one x hx)
  le_one := fun x hx => by linarith [hh.nonneg x hx]
  mass := hh.complement_mass

theorem contrast_norm_sq_le {h : ℝ → ℝ} (hh : Admissible h) (ξ : ℝ) :
    contrastCos h ξ ^ 2 + contrastSin h ξ ^ 2 ≤ 4 * (1 - Real.sinc ξ ^ 2) := by
  have hH := trig_moment_norm_sq_le_one hh ξ
  have hG := trig_moment_norm_sq_le_one hh.complement ξ
  rw [cosMoment_complement hh ξ, sinMoment_complement hh ξ] at hG
  rw [contrastCos_eq hh ξ, contrastSin_eq hh ξ]
  nlinarith

theorem squarePairing_cos_lower {h : ℝ → ℝ} (hh : Admissible h) (ξ : ℝ) :
    2 * Real.sinc ξ ^ 2 - 1 ≤ squarePairing h (fun t => Real.cos (ξ * t)) := by
  rw [squarePairing_cos_identity hh ξ]
  linarith [contrast_norm_sq_le hh ξ]

theorem squarePairing_sin_abs_bound {h : ℝ → ℝ} (hh : Admissible h) (ξ : ℝ) :
    |squarePairing h (fun t => Real.sin (ξ * t))| ≤
      2 * |Real.sinc ξ| * Real.sqrt (1 - Real.sinc ξ ^ 2) := by
  have hn := contrast_norm_sq_le hh ξ
  have hnonneg : 0 ≤ 1 - Real.sinc ξ ^ 2 := by
    nlinarith [sq_nonneg (contrastCos h ξ), sq_nonneg (contrastSin h ξ)]
  have hsq := Real.sq_sqrt hnonneg
  have hsqrt := Real.sqrt_nonneg (1 - Real.sinc ξ ^ 2)
  have hs : |contrastSin h ξ| ≤ 2 * Real.sqrt (1 - Real.sinc ξ ^ 2) := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (contrastCos h ξ)]
  rw [squarePairing_sin_identity hh ξ, abs_mul, abs_neg]
  have hb := mul_le_mul_of_nonneg_left hs (abs_nonneg (Real.sinc ξ))
  nlinarith

/-- The phase-combined row used by the outer certificates follows by
completing the square in the exact physical Fourier remainder. -/
theorem squarePairing_cos_add_mul_sin_bound {h : ℝ → ℝ} (hh : Admissible h)
    (ξ α : ℝ) :
    squarePairing h (fun t => Real.cos (ξ * t)) +
        α * squarePairing h (fun t => Real.sin (ξ * t)) ≤
      (1 + α ^ 2) * Real.sinc ξ ^ 2 := by
  rw [squarePairing_cos_identity hh ξ, squarePairing_sin_identity hh ξ]
  nlinarith [sq_nonneg (contrastCos h ξ),
    sq_nonneg (contrastSin h ξ + 2 * α * Real.sinc ξ)]

@[expose] def densityFirstMoment (h : ℝ → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..2, h x * x

@[expose] def densitySecondMoment (h : ℝ → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..2, h x * x ^ 2

theorem Admissible.firstMoment_intervalIntegrable {h : ℝ → ℝ} (hh : Admissible h) :
    IntervalIntegrable (fun x => h x * x) volume 0 2 :=
  (hh.intervalIntegrable (by norm_num) (by norm_num) (by norm_num)).mul_continuousOn
    continuous_id.continuousOn

theorem Admissible.secondMoment_intervalIntegrable {h : ℝ → ℝ} (hh : Admissible h) :
    IntervalIntegrable (fun x => h x * x ^ 2) volume 0 2 :=
  (hh.intervalIntegrable (by norm_num) (by norm_num) (by norm_num)).mul_continuousOn
    (continuous_id.pow 2).continuousOn

theorem densityFirstMoment_complement {h : ℝ → ℝ} (hh : Admissible h) :
    densityFirstMoment (fun x => 1 - h x) = 2 - densityFirstMoment h := by
  unfold densityFirstMoment
  simp only [sub_mul, one_mul]
  have hi : IntervalIntegrable (fun x : ℝ => x) volume 0 2 := continuous_id.intervalIntegrable 0 2
  rw [intervalIntegral.integral_sub hi
    hh.firstMoment_intervalIntegrable, integral_id]
  norm_num

theorem densitySecondMoment_complement {h : ℝ → ℝ} (hh : Admissible h) :
    densitySecondMoment (fun x => 1 - h x) = 8 / 3 - densitySecondMoment h := by
  unfold densitySecondMoment
  simp only [sub_mul, one_mul]
  have hi : IntervalIntegrable (fun x : ℝ => x ^ 2) volume 0 2 := (continuous_id.pow 2).intervalIntegrable 0 2
  rw [intervalIntegral.integral_sub hi
    hh.secondMoment_intervalIntegrable, integral_pow]
  norm_num

theorem squarePairing_one {h : ℝ → ℝ} (hh : Admissible h) :
    squarePairing h (fun _ => 1) = 1 := by
  unfold squarePairing
  simp only [mul_one]
  simp_rw [intervalIntegral.integral_const_mul, hh.complement_mass, mul_one]
  exact hh.mass

theorem quartetFunctional_one {h : ℝ → ℝ} (hh : Admissible h) :
    quartetFunctional h (fun _ => 1) = 1 := by
  rw [← squarePairing_eq_quartetFunctional_of_continuous hh continuous_const
    (fun _ => rfl)]
  exact squarePairing_one hh

theorem squarePairing_id {h : ℝ → ℝ} (hh : Admissible h) :
    squarePairing h (fun t => t) = 2 - 2 * densityFirstMoment h := by
  have hg₁ : IntervalIntegrable (fun x => (1 - h x) * x) volume 0 2 :=
    hh.complement_intervalIntegrable.mul_continuousOn continuous_id.continuousOn
  have hinner (x : ℝ) :
      (∫ y in (0 : ℝ)..2, h x * (1 - h y) * (y - x)) =
        h x * densityFirstMoment (fun y => 1 - h y) - h x * x := by
    calc
      _ = ∫ y in (0 : ℝ)..2,
          h x * ((1 - h y) * y) - (h x * x) * (1 - h y) := by
        apply intervalIntegral.integral_congr
        intro y _
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub (hg₁.const_mul (h x))
          (hh.complement_intervalIntegrable.const_mul (h x * x)),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          hh.complement_mass, mul_one]
        rfl
  unfold squarePairing
  simp_rw [hinner]
  rw [intervalIntegral.integral_sub
    ((hh.intervalIntegrable (by norm_num) (by norm_num) (by norm_num)).mul_const _)
    hh.firstMoment_intervalIntegrable,
    intervalIntegral.integral_mul_const, hh.mass, one_mul,
    densityFirstMoment_complement hh]
  unfold densityFirstMoment
  ring

theorem profileMean_eq_densityFirstMoment {h : ℝ → ℝ} (hh : Admissible h) :
    profileMean (overlapProfile h) = 2 - 2 * densityFirstMoment h := by
  have hid : squarePairing h (fun t => t) = overlapFirstMoment h := by
    rw [squarePairing_eq_signedOverlapPairing_of_continuous (K := fun t => t) hh continuous_id]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only [signedOverlapIntegrand]
    ring
  rw [← overlapFirstMoment_eq_profileMean hh, ← hid, squarePairing_id hh]

theorem squarePairing_sq {h : ℝ → ℝ} (hh : Admissible h) :
    squarePairing h (fun t => t ^ 2) =
      8 / 3 - 4 * densityFirstMoment h + 2 * densityFirstMoment h ^ 2 := by
  have hg₁ : IntervalIntegrable (fun x => (1 - h x) * x) volume 0 2 :=
    hh.complement_intervalIntegrable.mul_continuousOn continuous_id.continuousOn
  have hg₂ : IntervalIntegrable (fun x => (1 - h x) * x ^ 2) volume 0 2 :=
    hh.complement_intervalIntegrable.mul_continuousOn (continuous_id.pow 2).continuousOn
  have hinner (x : ℝ) :
      (∫ y in (0 : ℝ)..2, h x * (1 - h y) * (y - x) ^ 2) =
        h x * densitySecondMoment (fun y => 1 - h y) -
          (2 * (h x * x)) * densityFirstMoment (fun y => 1 - h y) + h x * x ^ 2 := by
    calc
      _ = ∫ y in (0 : ℝ)..2,
          (h x * ((1 - h y) * y ^ 2) -
            (2 * (h x * x)) * ((1 - h y) * y)) +
            (h x * x ^ 2) * (1 - h y) := by
        apply intervalIntegral.integral_congr
        intro y _
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add
          ((hg₂.const_mul (h x)).sub (hg₁.const_mul (2 * (h x * x))))
          (hh.complement_intervalIntegrable.const_mul (h x * x ^ 2)),
          intervalIntegral.integral_sub (hg₂.const_mul (h x))
            (hg₁.const_mul (2 * (h x * x))),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul, hh.complement_mass, mul_one]
        rfl
  unfold squarePairing
  simp_rw [hinner]
  rw [intervalIntegral.integral_add
    (((hh.intervalIntegrable (by norm_num) (by norm_num) (by norm_num)).mul_const _).sub
      ((hh.firstMoment_intervalIntegrable.const_mul 2).mul_const _))
    hh.secondMoment_intervalIntegrable,
    intervalIntegral.integral_sub
      ((hh.intervalIntegrable (by norm_num) (by norm_num) (by norm_num)).mul_const _)
      ((hh.firstMoment_intervalIntegrable.const_mul 2).mul_const _),
    intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_const_mul, hh.mass, one_mul,
    densitySecondMoment_complement hh, densityFirstMoment_complement hh]
  unfold densityFirstMoment densitySecondMoment
  ring

/-- Exact second moment identity with the physical folded mean. -/
theorem quartetFunctional_sq {h : ℝ → ℝ} (hh : Admissible h) :
    quartetFunctional h (fun t => t ^ 2) =
      2 / 3 + profileMean (overlapProfile h) ^ 2 / 2 := by
  rw [← squarePairing_eq_quartetFunctional_of_continuous (K := fun t => t ^ 2) hh
    (continuous_id.pow 2) (fun t => neg_sq t),
    squarePairing_sq hh, profileMean_eq_densityFirstMoment hh]
  ring

end
end
end ErdosOverlap
