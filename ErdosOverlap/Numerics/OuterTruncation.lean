/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.OuterCell

/-! # Certified truncation of the shared outer Taylor polynomials

On the normalized cell `|u| ≤ 1`, deleting a polynomial tail costs at most
the exact sum of the absolute values of its rational coefficients.
-/

@[expose] public section

namespace ErdosOverlap.Numerics

def coefficientAbsSum : List ℚ → ℚ
  | [] => 0
  | c :: cs => |c| + coefficientAbsSum cs

theorem coefficientAbsSum_nonneg (cs : List ℚ) : 0 ≤ coefficientAbsSum cs := by
  induction cs with
  | nil => exact le_rfl
  | cons c cs ih => exact add_nonneg (abs_nonneg c) ih

theorem polynomialValue_abs_le_coefficientAbsSum (cs : List ℚ) {u : ℝ}
    (hu : |u| ≤ 1) : |polynomialValue cs u| ≤ (coefficientAbsSum cs : ℝ) := by
  induction cs with
  | nil => simp [polynomialValue, coefficientAbsSum]
  | cons c cs ih =>
    simp only [polynomialValue, coefficientAbsSum, Rat.cast_add, Rat.cast_abs]
    apply (abs_add_le _ _).trans
    apply add_le_add le_rfl
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right hu (abs_nonneg _)).trans (by simpa using ih)

theorem polynomialValue_sub_take_abs_le (cs : List ℚ) (n : ℕ) {u : ℝ}
    (hu : |u| ≤ 1) :
    |polynomialValue cs u - polynomialValue (cs.take n) u| ≤
      (coefficientAbsSum (cs.drop n) : ℝ) := by
  induction n generalizing cs with
  | zero =>
    simpa [polynomialValue] using polynomialValue_abs_le_coefficientAbsSum cs hu
  | succ n ih =>
    cases cs with
    | nil => simp [polynomialValue, coefficientAbsSum]
    | cons c cs =>
      simp only [List.take_succ_cons, List.drop_succ_cons, polynomialValue]
      rw [show (c : ℝ) + u * polynomialValue cs u -
          ((c : ℝ) + u * polynomialValue (cs.take n) u) =
          u * (polynomialValue cs u - polynomialValue (cs.take n) u) by ring,
        abs_mul]
      exact (mul_le_mul_of_nonneg_right hu (abs_nonneg _)).trans
        (by simpa using ih cs)

end ErdosOverlap.Numerics

namespace ErdosOverlap
open Numerics

theorem OuterCellModel.correct_of_basis_truncated (m : OuterCellModel)
    (p : OuterFourierPolynomial) {basis : List LocalTrigApprox}
    (hb : ∀ a ∈ basis, a.Correct m.center m.radius)
    (hr : m.radius ≠ 0) (n : ℕ)
    (hcs : m.coefficients = (p.compiledCoefficients basis).take n)
    (he : p.compiledError basis +
      coefficientAbsSum ((p.compiledCoefficients basis).drop n) ≤ m.error) :
    m.Correct p := by
  intro t ht
  have hbase := p.compiled_value_error hb hr ht
  have htail := polynomialValue_sub_take_abs_le (p.compiledCoefficients basis) n ht
  have he' : (p.compiledError basis : ℝ) +
      (coefficientAbsSum ((p.compiledCoefficients basis).drop n) : ℝ) ≤ m.error := by
    exact_mod_cast he
  have hd : (p.approximation (p.compiledCoefficients basis) m.center m.radius).value t -
      (m.polynomial p).value t =
      polynomialValue (p.compiledCoefficients basis) ((t-(m.center : ℝ))/(m.radius : ℝ)) -
      polynomialValue ((p.compiledCoefficients basis).take n)
        ((t-(m.center : ℝ))/(m.radius : ℝ)) := by
    unfold OuterCellModel.polynomial
    rw [hcs]
    simp only [OuterFourierPolynomial.approximation,
      quadraticPatch_value _ m.center m.radius p.constant p.linear p.quadratic hr]
    ring
  calc
    |p.value t - (m.polynomial p).value t| ≤
        |p.value t - (p.approximation (p.compiledCoefficients basis) m.center m.radius).value t| +
        |(p.approximation (p.compiledCoefficients basis) m.center m.radius).value t -
          (m.polynomial p).value t| := abs_sub_le _ _ _
    _ ≤ (p.compiledError basis : ℝ) +
        (coefficientAbsSum ((p.compiledCoefficients basis).drop n) : ℝ) := by
      rw [hd]
      exact add_le_add hbase htail
    _ ≤ (m.error : ℝ) := he'

end ErdosOverlap
