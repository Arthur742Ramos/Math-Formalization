/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.IntegralClaimBlock

/-!
# Final exact rounding of a full-interval integral certificate

The finite check verifies both endpoints and compares the claimed rational
bound with the exact integer total after the proved uniform error correction.
-/

@[expose] public section

namespace ErdosOverlap.Numerics.IntegralClaim

open MeasureTheory

def lowerFinalCheck (c : IntegralClaim) (error bound : ℚ) : Bool :=
  decide (c.left = 0 ∧ c.right = 1 ∧ bound ≤ (c.amount : ℚ)/fixedScale-error)

def upperFinalCheck (c : IntegralClaim) (error bound : ℚ) : Bool :=
  decide (c.left = 0 ∧ c.right = 1 ∧ (c.amount : ℚ)/fixedScale+error ≤ bound)

theorem LowerCertificate.full_bound {f : ℝ → ℝ} {error bound : ℚ} {c : IntegralClaim}
    (hc : LowerCertificate f error c) (hcheck : lowerFinalCheck c error bound = true) :
    (bound : ℝ) ≤ ∫ t in (0 : ℝ)..1, f t := by
  have hs : c.left = 0 ∧ c.right = 1 ∧ bound ≤ (c.amount : ℚ)/fixedScale-error :=
    of_decide_eq_true hcheck
  have hi : (((c.amount : ℚ)/fixedScale-error : ℚ) : ℝ) ≤ ∫ t in (0 : ℝ)..1, f t := by
    simpa only [hs.1, hs.2.1, sub_zero, mul_one, Rat.cast_zero, Rat.cast_one] using hc.bound
  exact ((Rat.cast_le (K := ℝ)).2 hs.2.2).trans hi

theorem UpperCertificate.full_bound {f : ℝ → ℝ} {error bound : ℚ} {c : IntegralClaim}
    (hc : UpperCertificate f error c) (hcheck : upperFinalCheck c error bound = true) :
    (∫ t in (0 : ℝ)..1, f t) ≤ (bound : ℝ) := by
  have hs : c.left = 0 ∧ c.right = 1 ∧ (c.amount : ℚ)/fixedScale+error ≤ bound :=
    of_decide_eq_true hcheck
  have hi : (∫ t in (0 : ℝ)..1, f t) ≤ (((c.amount : ℚ)/fixedScale+error : ℚ) : ℝ) := by
    simpa only [hs.1, hs.2.1, sub_zero, mul_one, Rat.cast_zero, Rat.cast_one] using hc.bound
  exact hi.trans ((Rat.cast_le (K := ℝ)).2 hs.2.2)

end ErdosOverlap.Numerics.IntegralClaim
