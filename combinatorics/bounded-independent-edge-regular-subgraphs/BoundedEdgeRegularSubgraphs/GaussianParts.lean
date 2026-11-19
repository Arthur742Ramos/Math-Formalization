module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# One-dimensional Gaussian integration by parts and moments
-/

@[expose] public section

open MeasureTheory

namespace BoundedEdgeRegularSubgraphs

/-- The unnormalised density of a standard normal. -/
noncomputable def standardNormalKernel (x : ℝ) : ℝ := Real.exp (-(x ^ 2 / 2))

private theorem hasDerivAt_standardNormalKernel (x : ℝ) :
    HasDerivAt standardNormalKernel (-x * standardNormalKernel x) x := by
  have h : HasDerivAt (fun y : ℝ ↦ -(y ^ 2 / 2)) (-x) x := by
    change HasDerivAt (-(fun y : ℝ ↦ y ^ 2 / 2)) (-x) x
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_div_cancel_left₀
      _ (by norm_num : (2 : ℝ) ≠ 0)] using ((hasDerivAt_pow 2 x).div_const (2 : ℝ)).neg
  have hh := (Real.hasDerivAt_exp (-(x ^ 2 / 2))).comp x h
  change HasDerivAt (Real.exp ∘ fun y : ℝ ↦ -(y ^ 2 / 2))
    (-x * Real.exp (-(x ^ 2 / 2))) x
  simpa only [mul_comm] using hh

/-- Integration by parts with the Gaussian density. The assumptions are
integrability of the function and the two terms in the derivative identity. -/
theorem integral_standardNormalKernel_deriv (f f' : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hi : Integrable (fun x ↦ standardNormalKernel x * f x))
    (hi' : Integrable (fun x ↦ standardNormalKernel x * f' x))
    (hxi : Integrable (fun x ↦ x * standardNormalKernel x * f x)) :
    (∫ x, standardNormalKernel x * f' x) = ∫ x, x * standardNormalKernel x * f x := by
  have hxi' : Integrable (fun x ↦ -x * standardNormalKernel x * f x) := by
    have he : (fun x ↦ -x * standardNormalKernel x * f x) =
        -(fun x ↦ x * standardNormalKernel x * f x) := by
      funext x
      simp only [Pi.neg_apply, neg_mul]
    rw [he]
    exact hxi.neg
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := standardNormalKernel) (u' := fun x ↦ -x * standardNormalKernel x)
    (v := f) (v' := f')
    (fun x _ ↦ hasDerivAt_standardNormalKernel x) (fun x _ ↦ hf x) hi' hxi' hi
  simpa only [neg_mul, integral_neg, neg_neg] using h

/-- Every polynomial moment is integrable against the Gaussian density. -/
theorem integrable_pow_mul_standardNormalKernel (m : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ m * standardNormalKernel x) := by
  have hb : (0 : ℝ) < 1 / 2 := by norm_num
  have hm : (-1 : ℝ) < m := (by norm_num : (-1 : ℝ) < 0).trans_le (Nat.cast_nonneg m)
  have hExp (x : ℝ) : -(x ^ 2 / 2) = -(1 / 2 : ℝ) * x ^ 2 := by ring
  simpa only [Real.rpow_natCast, standardNormalKernel, hExp] using
    integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 2) hb (s := (m : ℝ)) hm

/-- The Gaussian moments obey the recurrence used for the fourth and eighth moments. -/
theorem integral_pow_add_two_standardNormalKernel (m : ℕ) :
    (∫ x : ℝ, x ^ (m + 2) * standardNormalKernel x) =
      (m + 1 : ℝ) * ∫ x : ℝ, x ^ m * standardNormalKernel x := by
  let f (x : ℝ) := x ^ (m + 1)
  let f' (x : ℝ) := (m + 1 : ℝ) * x ^ m
  have hf (x : ℝ) : HasDerivAt f (f' x) x := by
    simpa only [f, f', Nat.cast_succ, Nat.add_sub_cancel, id_eq, mul_one] using
      hasDerivAt_pow (m + 1) x
  have h₀ : (fun x : ℝ ↦ standardNormalKernel x * f x) =
      fun x : ℝ ↦ x ^ (m + 1) * standardNormalKernel x := by
    funext x
    exact mul_comm _ _
  have h₁ : (fun x : ℝ ↦ standardNormalKernel x * f' x) =
      fun x : ℝ ↦ (m + 1 : ℝ) * (x ^ m * standardNormalKernel x) := by
    funext x
    dsimp only [f']
    ac_rfl
  have h₂ : (fun x : ℝ ↦ x * standardNormalKernel x * f x) =
      fun x : ℝ ↦ x ^ (m + 2) * standardNormalKernel x := by
    funext x
    dsimp only [f]
    rw [pow_succ x (m + 1)]
    ac_rfl
  have hi : Integrable (fun x ↦ standardNormalKernel x * f x) := by
    rw [h₀]
    exact integrable_pow_mul_standardNormalKernel (m + 1)
  have hi' : Integrable (fun x ↦ standardNormalKernel x * f' x) := by
    rw [h₁]
    exact (integrable_pow_mul_standardNormalKernel m).const_mul _
  have hxi : Integrable (fun x ↦ x * standardNormalKernel x * f x) := by
    rw [h₂]
    exact integrable_pow_mul_standardNormalKernel (m + 2)
  have h := integral_standardNormalKernel_deriv f f' hf hi hi' hxi
  change (∫ x, (fun y ↦ standardNormalKernel y * f' y) x) =
    ∫ x, (fun y ↦ y * standardNormalKernel y * f y) x at h
  rw [h₁, h₂, integral_const_mul] at h
  exact h.symm

end BoundedEdgeRegularSubgraphs
