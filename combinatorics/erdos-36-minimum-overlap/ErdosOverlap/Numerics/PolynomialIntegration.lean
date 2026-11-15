/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.CachedTrig
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Exact integration of finite rational Horner polynomials

The primitive coefficient lists are executable rational data. Their integral
identities are proved for arbitrary real endpoints and affine weights, then
transported to the normalized coordinate of any nonzero-radius cell.
-/

namespace ErdosOverlap.Numerics

open MeasureTheory

public section

@[expose] noncomputable def polynomialValue : List ℚ → ℝ → ℝ
  | [], _ => 0
  | c :: cs, x => (c : ℝ) + x * polynomialValue cs x

@[expose] def polynomialRatValue : List ℚ → ℚ → ℚ
  | [], _ => 0
  | c :: cs, x => c + x * polynomialRatValue cs x

@[expose] def primitiveTail (n : ℕ) : List ℚ → List ℚ
  | [] => []
  | c :: cs => (c / (n + 1 : ℕ)) :: primitiveTail (n + 1) cs

@[expose] def primitiveCoeffs (cs : List ℚ) : List ℚ := 0 :: primitiveTail 0 cs

@[expose] def weightedPrimitiveCoeffs (cs : List ℚ) : List ℚ :=
  0 :: 0 :: primitiveTail 1 cs

theorem polynomialValue_eq_hornerVal (cs : List ℚ) (x : ℝ) :
    polynomialValue cs x = LeanCert.Core.IntervalRat.hornerVal cs x := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [polynomialValue, LeanCert.Core.IntervalRat.hornerVal]
    rw [ih]
    rfl

theorem polynomialRatValue_cast (cs : List ℚ) (x : ℚ) :
    (polynomialRatValue cs x : ℝ) = polynomialValue cs (x : ℝ) := by
  induction cs with
  | nil => simp only [polynomialRatValue, polynomialValue, Rat.cast_zero]
  | cons c cs ih =>
    simp only [polynomialRatValue, polynomialValue, Rat.cast_add, Rat.cast_mul, ih]

theorem polynomialValue_continuous (cs : List ℚ) : Continuous (polynomialValue cs) := by
  induction cs with
  | nil => exact continuous_const
  | cons c cs ih => exact continuous_const.add (continuous_id.mul ih)

theorem polynomialValue_intervalIntegrable (cs : List ℚ) (a b : ℝ) :
    IntervalIntegrable (polynomialValue cs) volume a b :=
  (polynomialValue_continuous cs).intervalIntegrable a b

theorem pow_mul_polynomialValue_continuous (cs : List ℚ) (n : ℕ) :
    Continuous (fun x : ℝ => x ^ n * polynomialValue cs x) := by
  convert! (continuous_id.pow n).mul (polynomialValue_continuous cs) using 1

/-- Termwise polynomial integration with a shifted starting degree. -/
theorem integral_pow_mul_polynomialValue (cs : List ℚ) (n : ℕ) (a b : ℝ) :
    (∫ x in a..b, x ^ n * polynomialValue cs x) =
      b ^ (n + 1) * polynomialValue (primitiveTail n cs) b -
        a ^ (n + 1) * polynomialValue (primitiveTail n cs) a := by
  induction cs generalizing n with
  | nil => simp only [polynomialValue, primitiveTail, mul_zero, intervalIntegral.integral_zero, sub_self]
  | cons c cs ih =>
    have h₁ : IntervalIntegrable (fun x : ℝ => (c : ℝ) * x ^ n) volume a b := by
      convert! ((continuous_id.pow n).const_mul (c : ℝ)).intervalIntegrable (μ := volume) a b using 1
    have h₂ := (pow_mul_polynomialValue_continuous cs (n + 1)).intervalIntegrable
      (μ := volume) a b
    calc
      _ = ∫ x in a..b, (c : ℝ) * x ^ n + x ^ (n + 1) * polynomialValue cs x := by
        apply intervalIntegral.integral_congr
        intro x _
        simp only [polynomialValue, pow_succ]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add h₁ h₂, intervalIntegral.integral_const_mul,
          integral_pow, ih (n + 1)]
        simp only [primitiveTail, polynomialValue, Rat.cast_div, Rat.cast_add, Rat.cast_one, Rat.cast_natCast,
          Nat.cast_add, Nat.cast_one, pow_succ]
        ring

/-- The rational coefficient list `[0,c0,c1/2,...]` is an exact primitive. -/
theorem integral_polynomialValue (cs : List ℚ) (a b : ℝ) :
    (∫ x in a..b, polynomialValue cs x) =
      polynomialValue (primitiveCoeffs cs) b - polynomialValue (primitiveCoeffs cs) a := by
  have h := integral_pow_mul_polynomialValue cs 0 a b
  simpa only [pow_zero, one_mul, Nat.zero_add, pow_one, primitiveCoeffs,
    polynomialValue, Rat.cast_zero, zero_add] using h

/-- The rational list `[0,0,c0/2,c1/3,...]` integrates `x * P(x)`. -/
theorem integral_mul_polynomialValue (cs : List ℚ) (a b : ℝ) :
    (∫ x in a..b, x * polynomialValue cs x) =
      polynomialValue (weightedPrimitiveCoeffs cs) b -
        polynomialValue (weightedPrimitiveCoeffs cs) a := by
  have h := integral_pow_mul_polynomialValue cs 1 a b
  simpa only [Nat.reduceAdd, pow_one, weightedPrimitiveCoeffs, polynomialValue, Rat.cast_zero,
    zero_add, pow_two, mul_assoc] using h

theorem integral_affine_mul_polynomialValue (cs : List ℚ) (α β a b : ℝ) :
    (∫ x in a..b, (α + β * x) * polynomialValue cs x) =
      α * (polynomialValue (primitiveCoeffs cs) b - polynomialValue (primitiveCoeffs cs) a) +
      β * (polynomialValue (weightedPrimitiveCoeffs cs) b -
        polynomialValue (weightedPrimitiveCoeffs cs) a) := by
  have hi := polynomialValue_intervalIntegrable cs a b
  have hxi : IntervalIntegrable (fun x : ℝ => x * polynomialValue cs x) volume a b := by
    convert! (continuous_id.mul (polynomialValue_continuous cs)).intervalIntegrable
      (μ := volume) a b using 1
  calc
    _ = ∫ x in a..b, α * polynomialValue cs x + β * (x * polynomialValue cs x) := by
      apply intervalIntegral.integral_congr
      intro x _
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add (hi.const_mul α) (hxi.const_mul β),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        integral_polynomialValue, integral_mul_polynomialValue]

/-- Exact affine-weight integration on a normalized cell. The radius may
have either sign; interval orientation is handled by the change of variables. -/
theorem integral_normalized_affine_polynomialValue (cs : List ℚ)
    (α β center radius a b : ℝ) (hr : radius ≠ 0) :
    (∫ t in a..b, (α + β * t) * polynomialValue cs ((t - center) / radius)) =
      radius * ((α + β * center) *
        (polynomialValue (primitiveCoeffs cs) ((b - center) / radius) -
          polynomialValue (primitiveCoeffs cs) ((a - center) / radius)) +
        (β * radius) *
        (polynomialValue (weightedPrimitiveCoeffs cs) ((b - center) / radius) -
          polynomialValue (weightedPrimitiveCoeffs cs) ((a - center) / radius))) := by
  let F : ℝ → ℝ := fun x => ((α + β * center) + (β * radius) * x) * polynomialValue cs x
  calc
    _ = ∫ t in a..b, F ((t - center) / radius) := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only [F]
      congr 1
      field_simp [hr]
      ring
    _ = ∫ x in (a - center)..(b - center), F (x / radius) := by
      exact intervalIntegral.integral_comp_sub_right (fun x => F (x / radius)) center
    _ = radius * ∫ x in ((a - center) / radius)..((b - center) / radius), F x := by
      simpa only [smul_eq_mul] using intervalIntegral.integral_comp_div F hr
    _ = _ := by
      rw [integral_affine_mul_polynomialValue]

/-- Fixed-point Horner enclosures apply to the exact polynomial used here. -/
theorem polynomialValue_mem_hornerBoxes {x : ℝ} {I : FixedBox} (hx : x ∈ I)
    {cs : List ℚ} {boxes : List FixedBox}
    (hcoeff : List.Forall₂ (fun (q : ℚ) (J : FixedBox) => (q : ℝ) ∈ J) cs boxes) :
    polynomialValue cs x ∈ FixedBox.hornerBoxes I boxes := by
  rw [polynomialValue_eq_hornerVal]
  exact FixedBox.mem_hornerBoxes hx hcoeff

@[expose] def affinePolynomialIntegralRat (cs : List ℚ) (α β a b : ℚ) : ℚ :=
  α * (polynomialRatValue (primitiveCoeffs cs) b - polynomialRatValue (primitiveCoeffs cs) a) +
    β * (polynomialRatValue (weightedPrimitiveCoeffs cs) b -
      polynomialRatValue (weightedPrimitiveCoeffs cs) a)

theorem integral_affine_polynomialValue_rat (cs : List ℚ) (α β a b : ℚ) :
    (∫ x in (a : ℝ)..(b : ℝ), ((α : ℝ) + (β : ℝ) * x) * polynomialValue cs x) =
      (affinePolynomialIntegralRat cs α β a b : ℝ) := by
  rw [integral_affine_mul_polynomialValue]
  simp only [affinePolynomialIntegralRat, Rat.cast_add, Rat.cast_mul, Rat.cast_sub,
    polynomialRatValue_cast]

@[expose] def normalizedPolynomialIntegralRat (cs : List ℚ)
    (α β center radius a b : ℚ) : ℚ :=
  radius * affinePolynomialIntegralRat cs (α + β * center) (β * radius)
    ((a - center) / radius) ((b - center) / radius)

theorem integral_normalized_polynomialValue_rat (cs : List ℚ)
    (α β center radius a b : ℚ) (hr : radius ≠ 0) :
    (∫ t in (a : ℝ)..(b : ℝ), ((α : ℝ) + (β : ℝ) * t) *
      polynomialValue cs ((t - (center : ℝ)) / (radius : ℝ))) =
      (normalizedPolynomialIntegralRat cs α β center radius a b : ℝ) := by
  have hrr : (radius : ℝ) ≠ 0 := by exact_mod_cast hr
  rw [integral_normalized_affine_polynomialValue cs _ _ _ _ _ _ hrr]
  simp only [normalizedPolynomialIntegralRat, affinePolynomialIntegralRat,
    Rat.cast_add, Rat.cast_mul, Rat.cast_sub, Rat.cast_div, polynomialRatValue_cast]

end
end ErdosOverlap.Numerics
