/-
Copyright (c) 2026. Released under the BSD-3-Clause license.
-/
module

public import ErdosOverlap.Overlap
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# Real Fourier identities for the physical partition pair

The frequency convention is `cos (ξ * t)`, with no factor of `2 * π`.
The functions below are integrated on the actual square `[0,2] × [0,2]`.
The centered Fourier coefficients of `2*h-1` give an exact nonnegative
square remainder in the cosine inequality. No Fourier certificate is a
hypothesis of these results.
-/

namespace ErdosOverlap

open MeasureTheory Set
open scoped Interval

public section

noncomputable section

/-- Expectation of a difference test function under the physical pair of
complementary densities on `[0,2]`. -/
@[expose] def squarePairing (h K : ℝ → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..2, ∫ y in (0 : ℝ)..2,
    h x * (1 - h y) * K (y - x)

@[expose] def centeredCos (ξ x : ℝ) : ℝ := Real.cos (ξ * (x - 1))

@[expose] def centeredSin (ξ x : ℝ) : ℝ := Real.sin (ξ * (x - 1))

@[expose] def cosMoment (f : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..2, f x * centeredCos ξ x

@[expose] def sinMoment (f : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..2, f x * centeredSin ξ x

/-- Centered cosine coefficient of the contrast `2*h-1` on its support. -/
@[expose] def contrastCos (h : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  cosMoment (fun x => 2 * h x - 1) ξ

/-- Centered sine coefficient of the contrast `2*h-1` on its support. -/
@[expose] def contrastSin (h : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  sinMoment (fun x => 2 * h x - 1) ξ

theorem continuous_centeredCos (ξ : ℝ) : Continuous (centeredCos ξ) :=
  Real.continuous_cos.comp (continuous_const.mul (continuous_id.sub continuous_const))

theorem continuous_centeredSin (ξ : ℝ) : Continuous (centeredSin ξ) :=
  Real.continuous_sin.comp (continuous_const.mul (continuous_id.sub continuous_const))

theorem cosine_difference_centered (ξ x y : ℝ) :
    Real.cos (ξ * (y - x)) =
      centeredCos ξ x * centeredCos ξ y + centeredSin ξ x * centeredSin ξ y := by
  have harg : ξ * (y - x) = ξ * (y - 1) - ξ * (x - 1) := by ring
  rw [harg, Real.cos_sub]
  unfold centeredCos centeredSin
  ring

theorem sine_difference_centered (ξ x y : ℝ) :
    Real.sin (ξ * (y - x)) =
      centeredCos ξ x * centeredSin ξ y - centeredSin ξ x * centeredCos ξ y := by
  have harg : ξ * (y - x) = ξ * (y - 1) - ξ * (x - 1) := by ring
  rw [harg, Real.sin_sub]
  unfold centeredCos centeredSin
  ring

/-- The integral of the centered cosine includes the continuous zero-frequency
case through Mathlib's unnormalized sinc. -/
theorem integral_centeredCos (ξ : ℝ) :
    (∫ x in (0 : ℝ)..2, centeredCos ξ x) = 2 * Real.sinc ξ := by
  by_cases hξ : ξ = 0
  · subst ξ
    simp [centeredCos]
  · have hchange := intervalIntegral.integral_comp_mul_sub
      (f := Real.cos) (a := (0 : ℝ)) (b := 2) hξ ξ
    have hfun : (fun x : ℝ => centeredCos ξ x) =
        (fun x : ℝ => Real.cos (ξ * x - ξ)) := by
      funext x
      unfold centeredCos
      congr 1
      ring
    rw [hfun, hchange, integral_cos, Real.sinc_of_ne_zero hξ]
    simp only [mul_zero, zero_sub]
    have ht : ξ * 2 - ξ = ξ := by ring
    rw [ht, Real.sin_neg]
    simp only [smul_eq_mul]
    ring

theorem integral_centeredSin (ξ : ℝ) :
    (∫ x in (0 : ℝ)..2, centeredSin ξ x) = 0 := by
  by_cases hξ : ξ = 0
  · subst ξ
    simp [centeredSin]
  · have hchange := intervalIntegral.integral_comp_mul_sub
      (f := Real.sin) (a := (0 : ℝ)) (b := 2) hξ ξ
    have hfun : (fun x : ℝ => centeredSin ξ x) =
        (fun x : ℝ => Real.sin (ξ * x - ξ)) := by
      funext x
      unfold centeredSin
      congr 1
      ring
    rw [hfun, hchange, integral_sin]
    simp only [mul_zero, zero_sub]
    have ht : ξ * 2 - ξ = ξ := by ring
    rw [ht, Real.cos_neg, sub_self, smul_zero]

theorem Admissible.integrable_cosMoment {h : ℝ → ℝ} (hh : Admissible h) (ξ : ℝ) :
    IntervalIntegrable (fun x => h x * centeredCos ξ x) volume 0 2 :=
  (hh.intervalIntegrable (by norm_num) (by norm_num) (by norm_num)).mul_continuousOn
    (continuous_centeredCos ξ).continuousOn

theorem Admissible.integrable_sinMoment {h : ℝ → ℝ} (hh : Admissible h) (ξ : ℝ) :
    IntervalIntegrable (fun x => h x * centeredSin ξ x) volume 0 2 :=
  (hh.intervalIntegrable (by norm_num) (by norm_num) (by norm_num)).mul_continuousOn
    (continuous_centeredSin ξ).continuousOn

theorem Admissible.complement_intervalIntegrable {h : ℝ → ℝ} (hh : Admissible h) :
    IntervalIntegrable (fun x => 1 - h x) volume 0 2 :=
  intervalIntegrable_const.sub
    (hh.intervalIntegrable (by norm_num) (by norm_num) (by norm_num))

theorem cosMoment_complement {h : ℝ → ℝ} (hh : Admissible h) (ξ : ℝ) :
    cosMoment (fun x => 1 - h x) ξ = 2 * Real.sinc ξ - cosMoment h ξ := by
  unfold cosMoment
  simp only [sub_mul, one_mul]
  rw [intervalIntegral.integral_sub
    ((continuous_centeredCos ξ).intervalIntegrable 0 2) (hh.integrable_cosMoment ξ),
    integral_centeredCos]

theorem sinMoment_complement {h : ℝ → ℝ} (hh : Admissible h) (ξ : ℝ) :
    sinMoment (fun x => 1 - h x) ξ = -sinMoment h ξ := by
  unfold sinMoment
  simp only [sub_mul, one_mul]
  rw [intervalIntegral.integral_sub
    ((continuous_centeredSin ξ).intervalIntegrable 0 2) (hh.integrable_sinMoment ξ),
    integral_centeredSin, zero_sub]

theorem contrastCos_eq {h : ℝ → ℝ} (hh : Admissible h) (ξ : ℝ) :
    contrastCos h ξ = 2 * cosMoment h ξ - 2 * Real.sinc ξ := by
  unfold contrastCos cosMoment
  simp only [sub_mul, one_mul, mul_assoc]
  rw [intervalIntegral.integral_sub ((hh.integrable_cosMoment ξ).const_mul 2)
    ((continuous_centeredCos ξ).intervalIntegrable 0 2),
    intervalIntegral.integral_const_mul, integral_centeredCos]

theorem contrastSin_eq {h : ℝ → ℝ} (hh : Admissible h) (ξ : ℝ) :
    contrastSin h ξ = 2 * sinMoment h ξ := by
  unfold contrastSin sinMoment
  simp only [sub_mul, one_mul, mul_assoc]
  rw [intervalIntegral.integral_sub ((hh.integrable_sinMoment ξ).const_mul 2)
    ((continuous_centeredSin ξ).intervalIntegrable 0 2),
    intervalIntegral.integral_const_mul, integral_centeredSin, sub_zero]

/-- Factorization of the physical two-variable cosine pairing. Every
integrability condition follows from admissibility and bounded trigonometry. -/
theorem squarePairing_cos_factorization {h : ℝ → ℝ} (hh : Admissible h) (ξ : ℝ) :
    squarePairing h (fun t => Real.cos (ξ * t)) =
      cosMoment h ξ * cosMoment (fun x => 1 - h x) ξ +
        sinMoment h ξ * sinMoment (fun x => 1 - h x) ξ := by
  have hgc := hh.complement_intervalIntegrable.mul_continuousOn
    (continuous_centeredCos ξ).continuousOn
  have hgs := hh.complement_intervalIntegrable.mul_continuousOn
    (continuous_centeredSin ξ).continuousOn
  have hinner (x : ℝ) :
      (∫ y in (0 : ℝ)..2, h x * (1 - h y) * Real.cos (ξ * (y - x))) =
        (h x * centeredCos ξ x) * cosMoment (fun y => 1 - h y) ξ +
          (h x * centeredSin ξ x) * sinMoment (fun y => 1 - h y) ξ := by
    calc
      _ = ∫ y in (0 : ℝ)..2,
          (h x * centeredCos ξ x) * ((1 - h y) * centeredCos ξ y) +
            (h x * centeredSin ξ x) * ((1 - h y) * centeredSin ξ y) := by
        apply intervalIntegral.integral_congr
        intro y _
        dsimp only
        rw [cosine_difference_centered]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add
          (hgc.const_mul (h x * centeredCos ξ x))
          (hgs.const_mul (h x * centeredSin ξ x)),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
        rfl
  unfold squarePairing
  simp_rw [hinner]
  rw [intervalIntegral.integral_add
    ((hh.integrable_cosMoment ξ).mul_const _)
    ((hh.integrable_sinMoment ξ).mul_const _),
    intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
  rfl

/-- Exact real Fourier identity, retaining both nonnegative contrast squares.
This includes zero frequency and does not assume symmetry of the density. -/
theorem squarePairing_cos_identity {h : ℝ → ℝ} (hh : Admissible h) (ξ : ℝ) :
    squarePairing h (fun t => Real.cos (ξ * t)) =
      Real.sinc ξ ^ 2 - (contrastCos h ξ ^ 2 + contrastSin h ξ ^ 2) / 4 := by
  rw [squarePairing_cos_factorization hh ξ, cosMoment_complement hh ξ,
    sinMoment_complement hh ξ, contrastCos_eq hh ξ, contrastSin_eq hh ξ]
  ring

theorem squarePairing_cos_le_sinc_sq {h : ℝ → ℝ} (hh : Admissible h) (ξ : ℝ) :
    squarePairing h (fun t => Real.cos (ξ * t)) ≤ Real.sinc ξ ^ 2 := by
  rw [squarePairing_cos_identity hh ξ]
  nlinarith [sq_nonneg (contrastCos h ξ), sq_nonneg (contrastSin h ξ)]

/-- The direction required by every nonpositive native cosine multiplier. -/
theorem nonpositive_cosine_row {h : ℝ → ℝ} (hh : Admissible h)
    (ξ : ℝ) {z : ℝ} (hz : z ≤ 0) :
    z * Real.sinc ξ ^ 2 ≤ z * squarePairing h (fun t => Real.cos (ξ * t)) :=
  mul_le_mul_of_nonpos_left (squarePairing_cos_le_sinc_sq hh ξ) hz

theorem squarePairing_sin_factorization {h : ℝ → ℝ} (hh : Admissible h) (ξ : ℝ) :
    squarePairing h (fun t => Real.sin (ξ * t)) =
      cosMoment h ξ * sinMoment (fun x => 1 - h x) ξ -
        sinMoment h ξ * cosMoment (fun x => 1 - h x) ξ := by
  have hgc := hh.complement_intervalIntegrable.mul_continuousOn
    (continuous_centeredCos ξ).continuousOn
  have hgs := hh.complement_intervalIntegrable.mul_continuousOn
    (continuous_centeredSin ξ).continuousOn
  have hinner (x : ℝ) :
      (∫ y in (0 : ℝ)..2, h x * (1 - h y) * Real.sin (ξ * (y - x))) =
        (h x * centeredCos ξ x) * sinMoment (fun y => 1 - h y) ξ -
          (h x * centeredSin ξ x) * cosMoment (fun y => 1 - h y) ξ := by
    calc
      _ = ∫ y in (0 : ℝ)..2,
          (h x * centeredCos ξ x) * ((1 - h y) * centeredSin ξ y) -
            (h x * centeredSin ξ x) * ((1 - h y) * centeredCos ξ y) := by
        apply intervalIntegral.integral_congr
        intro y _
        dsimp only
        rw [sine_difference_centered]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub
          (hgs.const_mul (h x * centeredCos ξ x))
          (hgc.const_mul (h x * centeredSin ξ x)),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
        rfl
  unfold squarePairing
  simp_rw [hinner]
  rw [intervalIntegral.integral_sub
    ((hh.integrable_cosMoment ξ).mul_const _)
    ((hh.integrable_sinMoment ξ).mul_const _),
    intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
  rfl

theorem squarePairing_sin_identity {h : ℝ → ℝ} (hh : Admissible h) (ξ : ℝ) :
    squarePairing h (fun t => Real.sin (ξ * t)) =
      -Real.sinc ξ * contrastSin h ξ := by
  rw [squarePairing_sin_factorization hh ξ, cosMoment_complement hh ξ,
    sinMoment_complement hh ξ, contrastSin_eq hh ξ]
  ring

/-- A probability density has centered trigonometric moment in the unit
disk. The proof integrates the elementary inequality `cos ≤ 1`. -/
theorem trig_moment_norm_sq_le_one {h : ℝ → ℝ} (hh : Admissible h) (ξ : ℝ) :
    cosMoment h ξ ^ 2 + sinMoment h ξ ^ 2 ≤ 1 := by
  have hi := hh.intervalIntegrable (a := 0) (b := 2)
    (by norm_num) (by norm_num) (by norm_num)
  have hinner (x : ℝ) :
      (h x * centeredCos ξ x) * cosMoment h ξ +
          (h x * centeredSin ξ x) * sinMoment h ξ =
        h x * (∫ y in (0 : ℝ)..2, h y * Real.cos (ξ * (y - x))) := by
    calc
      _ = ∫ y in (0 : ℝ)..2,
          (h x * centeredCos ξ x) * (h y * centeredCos ξ y) +
            (h x * centeredSin ξ x) * (h y * centeredSin ξ y) := by
        rw [intervalIntegral.integral_add
          ((hh.integrable_cosMoment ξ).const_mul (h x * centeredCos ξ x))
          ((hh.integrable_sinMoment ξ).const_mul (h x * centeredSin ξ x)),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
        rfl
      _ = ∫ y in (0 : ℝ)..2, h x * (h y * Real.cos (ξ * (y - x))) := by
        apply intervalIntegral.integral_congr
        intro y _
        dsimp only
        rw [cosine_difference_centered]
        ring
      _ = _ := intervalIntegral.integral_const_mul _ _
  have hpoint : ∀ x ∈ Icc (0 : ℝ) 2,
      (h x * centeredCos ξ x) * cosMoment h ξ +
          (h x * centeredSin ξ x) * sinMoment h ξ ≤ h x := by
    intro x hx
    rw [hinner]
    have hc : Continuous (fun y : ℝ => Real.cos (ξ * (y - x))) :=
      Real.continuous_cos.comp (continuous_const.mul (continuous_id.sub continuous_const))
    have hint : IntervalIntegrable (fun y => h y * Real.cos (ξ * (y - x))) volume 0 2 :=
      hi.mul_continuousOn hc.continuousOn
    have hle := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 2) hint hi
      (fun y hy => mul_le_of_le_one_right (hh.nonneg y hy) (Real.cos_le_one _))
    rw [hh.mass] at hle
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hle (hh.nonneg x hx)
  have hle := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 2)
    (((hh.integrable_cosMoment ξ).mul_const _).add ((hh.integrable_sinMoment ξ).mul_const _))
    hi hpoint
  rw [intervalIntegral.integral_add ((hh.integrable_cosMoment ξ).mul_const _)
    ((hh.integrable_sinMoment ξ).mul_const _), intervalIntegral.integral_mul_const,
    intervalIntegral.integral_mul_const, hh.mass] at hle
  change cosMoment h ξ * cosMoment h ξ + sinMoment h ξ * sinMoment h ξ ≤ 1 at hle
  nlinarith

end

end

end ErdosOverlap
