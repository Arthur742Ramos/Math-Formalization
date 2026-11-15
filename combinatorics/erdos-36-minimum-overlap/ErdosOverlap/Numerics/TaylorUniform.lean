/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.QuantizedTaylor
public import ErdosOverlap.Numerics.PolynomialIntegration

/-!
# Uniform approximation by the checked quantized Taylor polynomial

This file adds the actual analytic remainders across the cosine terms and
adds the finite coefficient errors across the twenty polynomial degrees.
The resulting rational Horner polynomial is the one used by the exact
polynomial integration checker.
-/

namespace ErdosOverlap.Numerics

public section

@[expose] def cosineRemainderSum : List CosineTerm → ℚ → ℕ → ℚ
  | [], _, _ => 0
  | term :: terms, radius, n =>
      term.remainderBound radius n + cosineRemainderSum terms radius n

@[expose] def quantizedCoefficients (coefficients : List ℤ) : List ℚ :=
  coefficients.map (fun (p : ℤ) => (p : ℚ) / (quantizedCoefficientScale : ℚ))

@[expose] def taylorRemainderCheck (terms : List CosineTerm) : Bool :=
  decide (cosineRemainderSum terms taylorGridRadius 20 ≤ (1 / 10000000000000 : ℚ))

theorem taylorRemainderCheck_sound {terms : List CosineTerm}
    (h : taylorRemainderCheck terms = true) :
    cosineRemainderSum terms taylorGridRadius 20 ≤ (1 / 10000000000000 : ℚ) := by
  simpa only [taylorRemainderCheck, decide_eq_true_eq] using h

theorem cosineSum_localPolynomial_error (terms : List CosineTerm)
    (center radius : ℚ) (n : ℕ) {u : ℝ} (hu : |u| ≤ 1) :
    |cosineSum terms ((center : ℝ) + (radius : ℝ) * u) -
      ∑ k ∈ Finset.range n, cosineLocalCoefficientSum terms center radius k * u ^ k| ≤
      (cosineRemainderSum terms radius n : ℝ) := by
  induction terms with
  | nil =>
    simp only [cosineSum, cosineLocalCoefficientSum, zero_mul, Finset.sum_const_zero,
      sub_self, abs_zero, cosineRemainderSum, Rat.cast_zero, le_refl]
  | cons term terms ih =>
    have ht := term.localPolynomial_error center radius n hu
    have he : cosineSum (term :: terms) ((center : ℝ) + (radius : ℝ) * u) -
        ∑ k ∈ Finset.range n, cosineLocalCoefficientSum (term :: terms) center radius k * u ^ k =
        (term.value ((center : ℝ) + (radius : ℝ) * u) -
          term.localPolynomial center radius n u) +
        (cosineSum terms ((center : ℝ) + (radius : ℝ) * u) -
          ∑ k ∈ Finset.range n, cosineLocalCoefficientSum terms center radius k * u ^ k) := by
      simp only [cosineSum, cosineLocalCoefficientSum, CosineTerm.localPolynomial,
        add_mul, Finset.sum_add_distrib]
      ring
    rw [he]
    simpa only [cosineRemainderSum, Rat.cast_add] using
      (abs_add_le _ _).trans (add_le_add ht ih)

theorem polynomialValue_eq_sum_getD (coefficients : List ℚ) (u : ℝ) :
    polynomialValue coefficients u =
      ∑ k ∈ Finset.range coefficients.length, (coefficients.getD k 0 : ℝ) * u ^ k := by
  induction coefficients with
  | nil => simp only [polynomialValue, List.length_nil, Finset.range_zero, Finset.sum_empty]
  | cons c cs ih =>
    rw [polynomialValue, ih, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_zero, List.getD_cons_succ, pow_zero, mul_one, pow_succ]
    rw [Finset.mul_sum]
    have he : (∑ k ∈ Finset.range cs.length, u * ((cs.getD k 0 : ℝ) * u ^ k)) =
        ∑ k ∈ Finset.range cs.length, (cs.getD k 0 : ℝ) * (u ^ k * u) := by
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [he]
    ring

theorem polynomialCoefficient_sum_error (coefficients : List ℚ)
    (C : ℕ → ℝ) {ε u : ℝ} (hε : 0 ≤ ε) (hu : |u| ≤ 1)
    (hcoeff : ∀ k < coefficients.length, |C k - (coefficients.getD k 0 : ℝ)| ≤ ε) :
    |(∑ k ∈ Finset.range coefficients.length, C k * u ^ k) -
      polynomialValue coefficients u| ≤ (coefficients.length : ℝ) * ε := by
  rw [polynomialValue_eq_sum_getD, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    (∑ k ∈ Finset.range coefficients.length,
      |C k * u ^ k - (coefficients.getD k 0 : ℝ) * u ^ k|) ≤
      ∑ k ∈ Finset.range coefficients.length, ε := by
      apply Finset.sum_le_sum
      intro k hk
      rw [← sub_mul, abs_mul, abs_pow]
      have hp : |u| ^ k ≤ 1 := by
        simpa only [one_pow] using pow_le_pow_left₀ (abs_nonneg u) hu k
      exact (mul_le_mul_of_nonneg_right (hcoeff k (Finset.mem_range.mp hk))
        (pow_nonneg (abs_nonneg u) k)).trans
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hp hε)
    _ = (coefficients.length : ℝ) * ε := by simp

theorem quantizedCoefficients_length (coefficients : List ℤ) :
    (quantizedCoefficients coefficients).length = coefficients.length := by
  simp only [quantizedCoefficients, List.length_map]

theorem quantizedCoefficients_getD (coefficients : List ℤ) (k : ℕ) :
    ((quantizedCoefficients coefficients).getD k 0 : ℝ) =
      (coefficients.getD k 0 : ℝ) / (quantizedCoefficientScale : ℝ) := by
  induction coefficients generalizing k with
  | nil => simp [quantizedCoefficients]
  | cons p ps ih =>
    cases k with
    | zero =>
      simp only [quantizedCoefficients, List.map_cons, List.getD_cons_zero,
        Rat.cast_div, Rat.cast_intCast]
    | succ k =>
      simpa only [quantizedCoefficients, List.map_cons, List.getD_cons_succ] using ih k

/-- Twenty coefficient errors of at most `10⁻¹⁴`, together with a total
analytic remainder at most `10⁻¹³`, imply the advertised uniform `10⁻¹²`
error for the actual rational Horner polynomial. -/
theorem cosineSum_quantizedTaylor_error {terms : List CosineTerm}
    {coefficients : List ℤ} {j : ℕ}
    (hlen : coefficients.length = 20)
    (hcoeff : ∀ k < 20,
      |cosineLocalCoefficientSum terms (taylorGridCenter j) taylorGridRadius k -
        (coefficients.getD k 0 : ℝ) / (quantizedCoefficientScale : ℝ)| ≤
        1 / (quantizedCoefficientToleranceDenominator : ℝ))
    (hrem : cosineRemainderSum terms taylorGridRadius 20 ≤ (1 / 10000000000000 : ℚ))
    {u : ℝ} (hu : |u| ≤ 1) :
    |cosineSum terms ((taylorGridCenter j : ℝ) + (taylorGridRadius : ℝ) * u) -
      polynomialValue (quantizedCoefficients coefficients) u| ≤
      (1 / 1000000000000 : ℝ) := by
  have hrealrem : (cosineRemainderSum terms taylorGridRadius 20 : ℝ) ≤
      (1 / 10000000000000 : ℝ) := by
    have hcast : (cosineRemainderSum terms taylorGridRadius 20 : ℝ) ≤
        ((1 / 10000000000000 : ℚ) : ℝ) := Rat.cast_le.mpr hrem
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hcast
    exact hcast
  have hε : (0 : ℝ) ≤ 1 / (quantizedCoefficientToleranceDenominator : ℝ) := by
    norm_num [quantizedCoefficientToleranceDenominator]
  have hpoly := polynomialCoefficient_sum_error (quantizedCoefficients coefficients)
    (cosineLocalCoefficientSum terms (taylorGridCenter j) taylorGridRadius) hε hu
    (fun k hk => by
      rw [quantizedCoefficients_getD]
      apply hcoeff k
      simpa only [quantizedCoefficients_length, hlen] using hk)
  rw [quantizedCoefficients_length, hlen] at hpoly
  have htrue := cosineSum_localPolynomial_error terms (taylorGridCenter j)
    taylorGridRadius 20 hu
  have htriangle := abs_sub_le
    (cosineSum terms ((taylorGridCenter j : ℝ) + (taylorGridRadius : ℝ) * u))
    (∑ k ∈ Finset.range 20,
      cosineLocalCoefficientSum terms (taylorGridCenter j) taylorGridRadius k * u ^ k)
    (polynomialValue (quantizedCoefficients coefficients) u)
  norm_num only [quantizedCoefficientToleranceDenominator, Int.cast_ofNat,
    Nat.cast_ofNat] at hpoly
  linarith

/-- End-to-end generic interface from the checked factor and coefficient
rows to a true continuous-cell approximation. -/
theorem cosineSum_quantizedTaylor_error_of_checks {terms : List CosineTerm}
    {coefficients : List ℤ} {factors : ℕ → List ℤ} {row : List (ℤ × ℤ)} {j : ℕ}
    (hlen : coefficients.length = 20)
    (hf : ∀ k < 20, FactorRowCorrect terms k (factors k))
    (hr : RowTrigCorrect terms row j)
    (hcheck : ∀ k < 20,
      coefficientCheck (factors k) row j k (coefficients.getD k 0) = true)
    (hrem : taylorRemainderCheck terms = true) {u : ℝ} (hu : |u| ≤ 1) :
    |cosineSum terms ((taylorGridCenter j : ℝ) + (taylorGridRadius : ℝ) * u) -
      polynomialValue (quantizedCoefficients coefficients) u| ≤
      (1 / 1000000000000 : ℝ) := by
  apply cosineSum_quantizedTaylor_error hlen _ (taylorRemainderCheck_sound hrem) hu
  intro k hk
  exact coefficientCheck_sound (hf k hk) hr (hcheck k hk)

end
end ErdosOverlap.Numerics
