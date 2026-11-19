module

public import BoundedEdgeRegularSubgraphs.SymmetricMean
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-!
# Exponential moments of the restricted tilt
-/

public section

open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

private theorem exp_le_one_add_twice_of_nonneg_le_half {x : ℝ}
    (hx : 0 ≤ x) (hx₁ : x ≤ 1 / 2) : Real.exp x ≤ 1 + 2 * x := by
  have h := Real.exp_bound_div_one_sub_of_interval hx (by linarith)
  refine h.trans ((div_le_iff₀ (show 0 < 1 - x by linarith)).mpr ?_)
  nlinarith only [mul_nonneg hx (show 0 ≤ 1 - 2 * x by linarith only [hx₁])]

/-- When the maximum potential is small on the overlap scale, the
uniform restricted tilt has a bounded exponential moment. -/
theorem sum_restricted_tilt_exp_le {α : Type*} [DecidableEq α]
    (S : Finset α) (θ : α → ℝ) {A c : ℝ} (hA : 0 ≤ A) (hc : 0 ≤ c) (j : ℕ)
    (hS : S.Nonempty) (h₂ : (∑ i ∈ S, θ i ^ 2) ≤ A)
    (hinf : ∀ i ∈ S, c * (j : ℝ) * θ i ^ 2 ≤ 1 / 2) :
    (∑ J ∈ S.powersetCard j, Real.exp (c * (j : ℝ) * ∑ i ∈ J, θ i ^ 2)) ≤
      (S.card.choose j : ℝ) * Real.exp (2 * c * A * (j : ℝ) ^ 2 / S.card) := by
  let w (i : α) := Real.exp (c * (j : ℝ) * θ i ^ 2)
  have hk : 0 < (S.card : ℝ) := Nat.cast_pos.mpr hS.card_pos
  have hProd (J : Finset α) : Real.exp (c * (j : ℝ) * ∑ i ∈ J, θ i ^ 2) =
      ∏ i ∈ J, w i := by
    rw [Finset.mul_sum, Real.exp_sum]
  simp_rw [hProd]
  refine (sum_powersetCard_prod_le_choose_mean_pow S w (fun _ _ ↦ Real.exp_nonneg _) j).trans ?_
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have hsum : (∑ i ∈ S, w i) ≤ (S.card : ℝ) + 2 * c * (j : ℝ) * A := by
    calc
      _ ≤ ∑ i ∈ S, (1 + 2 * (c * (j : ℝ) * θ i ^ 2)) :=
        Finset.sum_le_sum (fun i hi ↦ exp_le_one_add_twice_of_nonneg_le_half (by positivity) (hinf i hi))
      _ = (S.card : ℝ) + 2 * c * (j : ℝ) * ∑ i ∈ S, θ i ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl (fun _ _ ↦ by ring)
      _ ≤ _ := add_le_add_right
        (mul_le_mul_of_nonneg_left h₂ (show 0 ≤ 2 * c * (j : ℝ) by positivity)) _
  have hm : (∑ i ∈ S, w i) / (S.card : ℝ) ≤ Real.exp (2 * c * (j : ℝ) * A / S.card) := by
    refine (div_le_div_of_nonneg_right hsum hk.le).trans ?_
    rw [add_div, div_self hk.ne', add_comm 1]
    exact Real.add_one_le_exp _
  rw [show 2 * c * A * (j : ℝ) ^ 2 / (S.card : ℝ) =
    (j : ℝ) * (2 * c * (j : ℝ) * A / S.card) by ring, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (div_nonneg (Finset.sum_nonneg (fun _ _ ↦ Real.exp_nonneg _)) hk.le) hm j

end BoundedEdgeRegularSubgraphs
