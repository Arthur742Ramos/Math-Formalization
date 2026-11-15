/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.PositiveLine
public import ErdosOverlap.AffineCompiler

/-!
# Exact polynomial patches for the native kernel pieces

The cosine approximation is augmented by the exact affine and quadratic
terms. Translating those terms to the normalized coordinate introduces no
numerical error. Range and integral boxes refer to the resulting actual
rational polynomial and allow either sign of the normalization radius.
-/

namespace ErdosOverlap.Numerics

open MeasureTheory Set

public section

@[expose] def patchCoefficients (cs : List ℚ) (q0 q1 q2 : ℚ) : List ℚ :=
  (cs.getD 0 0 + q0) :: (cs.getD 1 0 + q1) :: (cs.getD 2 0 + q2) :: cs.drop 3

theorem patchCoefficients_length (cs : List ℚ) (q0 q1 q2 : ℚ) :
    (patchCoefficients cs q0 q1 q2).length = max 3 cs.length := by
  simp only [patchCoefficients, List.length_cons, List.length_drop]
  omega

theorem polynomialValue_patchCoefficients (cs : List ℚ) (q0 q1 q2 : ℚ) (u : ℝ) :
    polynomialValue (patchCoefficients cs q0 q1 q2) u =
      polynomialValue cs u + (q0 : ℝ) + (q1 : ℝ) * u + (q2 : ℝ) * u ^ 2 := by
  cases cs with
  | nil =>
    simp [patchCoefficients, polynomialValue]
    ring
  | cons c0 cs =>
    cases cs with
    | nil =>
      simp [patchCoefficients, polynomialValue]
      ring
    | cons c1 cs =>
      cases cs with
      | nil =>
        simp [patchCoefficients, polynomialValue]
        ring
      | cons c2 cs =>
        simp [patchCoefficients, polynomialValue]
        ring

structure PolynomialPiece where
  coefficients : List ℚ
  center : ℚ
  radius : ℚ
  deriving DecidableEq, Repr

@[expose] noncomputable def PolynomialPiece.value (p : PolynomialPiece) (t : ℝ) : ℝ :=
  polynomialValue p.coefficients ((t - (p.center : ℝ)) / (p.radius : ℝ))

@[expose] def quadraticPatch (cs : List ℚ) (center radius constant linear quadratic : ℚ) :
    PolynomialPiece :=
  ⟨patchCoefficients cs (constant + linear * center + quadratic * center ^ 2)
    (radius * (linear + 2 * quadratic * center)) (quadratic * radius ^ 2), center, radius⟩

@[expose] def affineKernelPatch (cs : List ℚ) (center radius y0 y2 : ℚ) (p : AffinePiece) :
    PolynomialPiece :=
  quadraticPatch cs center radius (y0 + p.constant) p.linear y2

theorem quadraticPatch_value (cs : List ℚ) (center radius constant linear quadratic : ℚ)
    (hr : radius ≠ 0) (t : ℝ) :
    (quadraticPatch cs center radius constant linear quadratic).value t =
      polynomialValue cs ((t - (center : ℝ)) / (radius : ℝ)) +
        (constant : ℝ) + (linear : ℝ) * t + (quadratic : ℝ) * t ^ 2 := by
  have hr' : (radius : ℝ) ≠ 0 := by exact_mod_cast hr
  have ht : (center : ℝ) + (radius : ℝ) * ((t - (center : ℝ)) / (radius : ℝ)) = t := by
    field_simp [hr']
    ring
  unfold PolynomialPiece.value quadraticPatch
  simp only []
  rw [polynomialValue_patchCoefficients]
  calc
    _ = polynomialValue cs ((t - (center : ℝ)) / (radius : ℝ)) + (constant : ℝ) +
        (linear : ℝ) * ((center : ℝ) + (radius : ℝ) * ((t - (center : ℝ)) / (radius : ℝ))) +
        (quadratic : ℝ) * ((center : ℝ) + (radius : ℝ) * ((t - (center : ℝ)) / (radius : ℝ))) ^ 2 := by
      push_cast
      ring
    _ = _ := by rw [ht]

theorem affineKernelPatch_value (cs : List ℚ) (center radius y0 y2 : ℚ) (p : AffinePiece)
    (hr : radius ≠ 0) (t : ℝ) :
    (affineKernelPatch cs center radius y0 y2 p).value t =
      (y0 : ℝ) + (y2 : ℝ) * t ^ 2 +
        polynomialValue cs ((t - (center : ℝ)) / (radius : ℝ)) + p.value t := by
  rw [affineKernelPatch, quadraticPatch_value cs center radius _ _ _ hr t]
  simp only [AffinePiece.value, Rat.cast_add]
  ring

theorem affineKernelPatch_error {Q C : ℝ → ℝ} (cs : List ℚ)
    (center radius y0 y2 : ℚ) (p : AffinePiece) (hr : radius ≠ 0)
    {t delta : ℝ}
    (hQ : Q t = (y0 : ℝ) + (y2 : ℝ) * t ^ 2 + C t + p.value t)
    (hC : |C t - polynomialValue cs ((t - (center : ℝ)) / (radius : ℝ))| ≤ delta) :
    |Q t - (affineKernelPatch cs center radius y0 y2 p).value t| ≤ delta := by
  rw [hQ, affineKernelPatch_value cs center radius y0 y2 p hr t]
  convert hC using 1
  congr 1
  ring

/-- The patch transports a true a.e. kernel identity and a true a.e. cosine
approximation without adding error. -/
theorem affineKernelPatch_error_ae {Q C : ℝ → ℝ} {s : Set ℝ} (cs : List ℚ)
    (center radius y0 y2 : ℚ) (p : AffinePiece) (hr : radius ≠ 0) {delta : ℝ}
    (hQ : ∀ᵐ t ∂volume.restrict s,
      Q t = (y0 : ℝ) + (y2 : ℝ) * t ^ 2 + C t + p.value t)
    (hC : ∀ᵐ t ∂volume.restrict s,
      |C t - polynomialValue cs ((t - (center : ℝ)) / (radius : ℝ))| ≤ delta) :
    ∀ᵐ t ∂volume.restrict s,
      |Q t - (affineKernelPatch cs center radius y0 y2 p).value t| ≤ delta := by
  filter_upwards [hQ, hC] with t hQt hCt
  exact affineKernelPatch_error cs center radius y0 y2 p hr hQt hCt

@[expose] def PolynomialPiece.normalizedBox (p : PolynomialPiece) (lo hi : ℚ) : FixedBox :=
  FixedBox.ofBounds (min ((lo - p.center) / p.radius) ((hi - p.center) / p.radius))
    (max ((lo - p.center) / p.radius) ((hi - p.center) / p.radius))

@[expose] def PolynomialPiece.rangeBox (p : PolynomialPiece) (lo hi : ℚ) : FixedBox :=
  polynomialBox p.coefficients (p.normalizedBox lo hi)

theorem PolynomialPiece.normalized_mem_box (p : PolynomialPiece) {lo hi : ℚ} {t : ℝ}
    (ht : t ∈ Icc (lo : ℝ) (hi : ℝ)) :
    (t - (p.center : ℝ)) / (p.radius : ℝ) ∈ p.normalizedBox lo hi := by
  apply FixedBox.mem_ofBounds
  simp only [Rat.cast_min, Rat.cast_max, Rat.cast_div, Rat.cast_sub]
  by_cases hr : 0 ≤ (p.radius : ℝ)
  · exact ⟨(min_le_left _ _).trans
      (div_le_div_of_nonneg_right (sub_le_sub_right ht.1 _) hr),
      (div_le_div_of_nonneg_right (sub_le_sub_right ht.2 _) hr).trans (le_max_right _ _)⟩
  · have hr' : (p.radius : ℝ) ≤ 0 := le_of_not_ge hr
    exact ⟨(min_le_right _ _).trans
      (div_le_div_of_nonpos_of_le hr' (sub_le_sub_right ht.2 _)),
      (div_le_div_of_nonpos_of_le hr' (sub_le_sub_right ht.1 _)).trans (le_max_left _ _)⟩

theorem PolynomialPiece.value_mem_rangeBox (p : PolynomialPiece) {lo hi : ℚ} {t : ℝ}
    (ht : t ∈ Icc (lo : ℝ) (hi : ℝ)) : p.value t ∈ p.rangeBox lo hi := by
  exact polynomial_mem_box p.coefficients (p.normalized_mem_box ht)

theorem PolynomialPiece.rangeBox_bounds (p : PolynomialPiece) {lo hi : ℚ} {t : ℝ}
    (ht : t ∈ Icc (lo : ℝ) (hi : ℝ)) :
    ((p.rangeBox lo hi).lowerRat : ℝ) ≤ p.value t ∧
      p.value t ≤ ((p.rangeBox lo hi).upperRat : ℝ) :=
  FixedBox.real_bounds (p.value_mem_rangeBox ht)

theorem PolynomialPiece.positiveLine_sound (p : PolynomialPiece) {lo hi : ℚ} {t : ℝ}
    (ht : t ∈ Icc (lo : ℝ) (hi : ℝ)) :
    max (p.value t) 0 ≤ (p.rangeBox lo hi).positiveLine.value (p.value t) :=
  FixedBox.positiveLine_sound (p.value_mem_rangeBox ht)

theorem PolynomialPiece.continuous (p : PolynomialPiece) : Continuous p.value :=
  normalizedPolynomialValue_continuous p.coefficients p.center p.radius

@[expose] def PolynomialPiece.integralBox (p : PolynomialPiece) (alpha beta lo hi : ℚ) : FixedBox :=
  normalizedIntegralBox p.coefficients alpha beta p.center p.radius lo hi

theorem PolynomialPiece.integral_mem_box (p : PolynomialPiece) (alpha beta lo hi : ℚ)
    (hr : p.radius ≠ 0) :
    (∫ t in (lo : ℝ)..(hi : ℝ), ((alpha : ℝ) + (beta : ℝ) * t) * p.value t) ∈
      p.integralBox alpha beta lo hi := by
  unfold PolynomialPiece.value
  rw [integral_normalized_polynomialValue_rat p.coefficients alpha beta p.center p.radius lo hi hr]
  exact normalizedIntegral_mem_box p.coefficients alpha beta p.center p.radius lo hi

@[expose] def PolynomialPiece.reflectTwo (p : PolynomialPiece) : PolynomialPiece :=
  ⟨p.coefficients, 2 - p.center, -p.radius⟩

theorem PolynomialPiece.reflectTwo_value (p : PolynomialPiece) (t : ℝ) :
    p.reflectTwo.value t = p.value (2 - t) := by
  unfold PolynomialPiece.value PolynomialPiece.reflectTwo
  simp only [Rat.cast_sub, Rat.cast_neg, Rat.cast_ofNat, div_neg]
  congr 1
  ring

end
end ErdosOverlap.Numerics
