module

public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Order.Interval.Finset.SuccPred
import Mathlib.Tactic

/-!
# Geometric overlap sums at the mean-square imbalance scale
-/

public section

open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

/-- The moderate-overlap sum in Theorem 3.2. The hypothesis on the
imbalance forces the geometric base to be at most a constant times μ^(3/4). -/
theorem moderate_overlap_sum_le_of_meanSquare {μ C D a : ℝ} (hμ : 0 < μ)
    (hC : 0 ≤ C) (ha : D * a ≤ -Real.log μ / 4) (k : ℕ)
    (hsmall : Real.exp D * μ ^ (3 / 4 : ℝ) ≤ 1 / 2) :
    (∑ j ∈ Finset.Icc 2 k, μ ^ j * (C * Real.exp ((D + D * a) * (j : ℝ)))) ≤
      2 * C * (Real.exp D) ^ 2 * μ ^ (3 / 2 : ℝ) := by
  let x := μ * Real.exp (D + D * a)
  let y := Real.exp D * μ ^ (3 / 4 : ℝ)
  have hx : 0 ≤ x := mul_nonneg hμ.le (Real.exp_nonneg _)
  have hy : 0 ≤ y := mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg hμ.le _)
  have hxy : x ≤ y := by
    calc
      x ≤ μ * Real.exp (D + -Real.log μ / 4) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (add_le_add_right ha D)) hμ.le
      _ = Real.exp (Real.log μ) * Real.exp (D + -Real.log μ / 4) :=
        congrArg (fun z ↦ z * Real.exp (D + -Real.log μ / 4)) (Real.exp_log hμ).symm
      _ = y := by
        dsimp only [y]
        rw [← Real.exp_add, Real.rpow_def_of_pos hμ, ← Real.exp_add]
        congr 1
        ring
  have hxsmall : x ≤ 1 / 2 := hxy.trans hsmall
  have he (j : ℕ) : μ ^ j * (C * Real.exp ((D + D * a) * (j : ℝ))) = C * x ^ j := by
    unfold x
    rw [mul_comm (D + D * a), Real.exp_nat_mul, mul_pow]
    ring
  simp_rw [he, ← Finset.mul_sum]
  have hsum : (∑ j ∈ Finset.Icc 2 k, x ^ j) ≤ x ^ 2 / (1 - x) := by
    rw [← Finset.Ico_succ_right_eq_Icc]
    exact geom_sum_Ico_le_of_lt_one hx (hxsmall.trans_lt (by norm_num))
  have hhalf : x ^ 2 / (1 - x) ≤ 2 * x ^ 2 := by
    apply (div_le_iff₀ (show 0 < 1 - x by linarith only [hxsmall])).mpr
    nlinarith only [mul_nonneg (sq_nonneg x) (show 0 ≤ 1 - 2 * x by linarith only [hxsmall])]
  calc
    _ ≤ C * (2 * x ^ 2) := mul_le_mul_of_nonneg_left (hsum.trans hhalf) hC
    _ ≤ C * (2 * y ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hxy 2) (by norm_num)) hC
    _ = _ := by
      dsimp only [y]
      rw [mul_pow, ← Real.rpow_mul_natCast hμ.le, show (3 / 4 : ℝ) * ((2 : ℕ) : ℝ) = 3 / 2 by norm_num]
      ring

/-- In the balanced case the moderate-overlap geometric base is linear
in μ, giving the quadratic failure contribution. -/
theorem moderate_overlap_sum_le_of_zero_imbalance {μ C D : ℝ} (hμ : 0 ≤ μ)
    (hC : 0 ≤ C) (k : ℕ) (hsmall : μ * Real.exp D ≤ 1 / 2) :
    (∑ j ∈ Finset.Icc 2 k, μ ^ j * (C * Real.exp (D * (j : ℝ)))) ≤
      2 * C * (Real.exp D) ^ 2 * μ ^ 2 := by
  let x := μ * Real.exp D
  have hx : 0 ≤ x := mul_nonneg hμ (Real.exp_nonneg _)
  have he (j : ℕ) : μ ^ j * (C * Real.exp (D * (j : ℝ))) = C * x ^ j := by
    unfold x
    rw [mul_comm D, Real.exp_nat_mul, mul_pow]
    ring
  simp_rw [he, ← Finset.mul_sum]
  have hsum : (∑ j ∈ Finset.Icc 2 k, x ^ j) ≤ x ^ 2 / (1 - x) := by
    rw [← Finset.Ico_succ_right_eq_Icc]
    exact geom_sum_Ico_le_of_lt_one hx (lt_of_le_of_lt hsmall (by norm_num))
  have hhalf : x ^ 2 / (1 - x) ≤ 2 * x ^ 2 := by
    have hs : x ≤ 1 / 2 := hsmall
    apply (div_le_iff₀ (show 0 < 1 - x by linarith only [hs])).mpr
    nlinarith only [mul_nonneg (sq_nonneg x) (show 0 ≤ 1 - 2 * x by linarith only [hs])]
  refine (mul_le_mul_of_nonneg_left (hsum.trans hhalf) hC).trans_eq ?_
  unfold x
  ring

/-- The large-overlap contribution in Theorem 3.2 after bounding the
intersection probability by the geometric base. -/
theorem large_overlap_sum_le_exp_of_meanSquare {k j₀ : ℕ} {g H C a b : ℝ}
    (hg : 0 < g) (hg₁ : g ≤ 1 / 2)
    (hj : (3 / 4 : ℝ) * k ≤ (j₀ : ℝ))
    (hglog : Real.log g ≤ b - H - Real.log k)
    (ha : C * a ≤ (3 / 4 : ℝ) * H) (hb : 8 * (C + (3 / 4 : ℝ) * b) ≤ Real.log k) :
    (∑ j ∈ Finset.Icc j₀ k, g ^ j) *
      Real.exp ((k : ℝ) * Real.log k / 2 + C * ((k : ℝ) + a * k)) ≤
      2 * Real.exp (-(k : ℝ) * Real.log k / 8) := by
  let B := (k : ℝ) * Real.log k / 2 + C * ((k : ℝ) + a * k)
  have hsum : (∑ j ∈ Finset.Icc j₀ k, g ^ j) ≤ g ^ j₀ / (1 - g) := by
    rw [← Finset.Ico_succ_right_eq_Icc]
    exact geom_sum_Ico_le_of_lt_one hg.le (hg₁.trans_lt (by norm_num))
  have hhalf : g ^ j₀ / (1 - g) ≤ 2 * g ^ j₀ := by
    apply (div_le_iff₀ (show 0 < 1 - g by linarith only [hg₁])).mpr
    nlinarith only [mul_nonneg (pow_nonneg hg.le j₀) (show 0 ≤ 1 - 2 * g by linarith only [hg₁])]
  have hlog₀ : Real.log g ≤ 0 := Real.log_nonpos hg.le (hg₁.trans (by norm_num))
  have hExp : B + (j₀ : ℝ) * Real.log g ≤ -(k : ℝ) * Real.log k / 8 := by
    have h₁ := mul_le_mul_of_nonpos_right hj hlog₀
    have h₂ := mul_le_mul_of_nonneg_left hglog (show 0 ≤ (3 / 4 : ℝ) * k by positivity)
    have h₃ := mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    have h₄ := mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    dsimp only [B]
    nlinarith only [h₁, h₂, h₃, h₄]
  refine (mul_le_mul_of_nonneg_right (hsum.trans hhalf) (Real.exp_nonneg B)).trans ?_
  rw [← Real.exp_log hg, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Real.exp_le_exp.mpr (by linarith only [hExp])

end BoundedEdgeRegularSubgraphs
