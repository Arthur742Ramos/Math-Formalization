/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.OuterCell
public import ErdosOverlap.SignedKernel

/-! # Reassembling the two signed halves of an outer denominator -/

namespace ErdosOverlap
open MeasureTheory Set
public section

theorem OuterFourierPolynomial.denominator_le_of_integral_bounds
    (p : OuterFourierPolynomial) {a b D : ℝ}
    (hp : (∫ t in (0 : ℝ)..2, max (p.value t) 0) ≤ a)
    (hn : (∫ t in (0 : ℝ)..2, max (p.reflect.value t) 0) ≤ b)
    (hD : a+b ≤ D) : signedKernelDenominator p.value ≤ D := by
  rw [signedKernelDenominator_fold p.continuous]
  have hreflect : (fun t : ℝ => max (p.value t) 0 + max (p.value (-t)) 0) =
      (fun t : ℝ => max (p.value t) 0 + max (p.reflect.value t) 0) := by
    funext t
    rw [OuterFourierPolynomial.reflect_value]
  rw [hreflect]
  rw [intervalIntegral.integral_add
    ((p.continuous.max continuous_const).intervalIntegrable 0 2)
    ((p.reflect.continuous.max continuous_const).intervalIntegrable 0 2)]
  exact (add_le_add hp hn).trans hD

theorem OuterFourierPolynomial.denominator_le_of_rational_integral_bounds
    (p : OuterFourierPolynomial) {a b D : ℚ}
    (hp : (∫ t in (0 : ℝ)..2, max (p.value t) 0) ≤ (a : ℝ))
    (hn : (∫ t in (0 : ℝ)..2, max (p.reflect.value t) 0) ≤ (b : ℝ))
    (hD : a+b ≤ D) : signedKernelDenominator p.value ≤ (D : ℝ) := by
  apply p.denominator_le_of_integral_bounds hp hn
  simpa only [Rat.cast_add] using (Rat.cast_le (K := ℝ)).2 hD

end
end ErdosOverlap
