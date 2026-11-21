module

public import RectangleScore
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace InducedDegreeRepetition.Approximation

open Finset
open scoped Classical
variable {X Y : Type*} {q : ℕ} [NeZero q]

/-- Rotate the two character values at zero and one symmetrically about the real axis. -/
theorem binary_rotation (hq : 3 ≤ q) : ∃ z : ℂ, ‖z‖ = 1 ∧
    ∀ t : ZMod q, t = 0 ∨ t = 1 → 1/2 ≤ (z * ZMod.stdAddChar t).re := by
  let a : ℝ := Real.pi/q
  let z := Complex.exp ((-a : ℝ)*Complex.I)
  have hq' : 3 ≤ (q:ℝ) := by exact_mod_cast hq
  have c : 1/2 ≤ Real.cos a := by
    rw [← Real.cos_pi_div_three]
    apply Real.cos_le_cos_of_nonneg_of_le_pi (by dsimp [a]; positivity) (by linarith [Real.pi_pos])
    exact div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hq'
  have one : ZMod.stdAddChar (1 : ZMod q) = Complex.exp ((2*a:ℝ)*Complex.I) := by
    have e := ZMod.stdAddChar_coe (N := q) (1 : ℤ)
    simp only [Int.cast_one,mul_one] at e
    rw [e]
    push_cast
    dsimp [a]
    push_cast
    ring_nf
  refine ⟨z,?_,?_⟩
  · simp [z,Complex.norm_exp]
  intro t ht
  rcases ht with rfl | rfl
  · simpa [z,Complex.exp_re] using c
  · rw [one]
    change _ ≤ (Complex.exp _ * Complex.exp _).re
    rw [← Complex.exp_add]
    simpa [Complex.exp_re,show -a+2*a = a by ring] using c

/-- Error at most one eighth already forces the one-quarter character bias
required for the constant-rectangle theorem. -/
theorem bias_from_errors (hq : 3 ≤ q) (A B : X → Y → ZMod q) (S : Finset X) (U : Finset Y)
    (binary : ∀ x ∈ S, ∀ y ∈ U, B x y = 0 ∨ B x y = 1)
    (low : errors (fun x y => A x y ≠ B x y) S U ≤ (1/8:ℝ)*S.card*U.card) :
    (S.card:ℝ)*U.card/4 ≤ ‖∑ x ∈ S, ∑ y ∈ U, ZMod.stdAddChar (A x y)‖ := by
  obtain ⟨z,hz,good⟩ := binary_rotation hq
  have bound (x) (hx : x ∈ S) (y) (hy : y ∈ U) :
      1/2 - 2 * (if A x y ≠ B x y then (1:ℝ) else 0) ≤ (z*ZMod.stdAddChar (A x y)).re := by
    by_cases h : A x y = B x y
    · simpa [h] using good _ (binary x hx y hy)
    · have n := Complex.abs_re_le_norm (z*ZMod.stdAddChar (A x y))
      rw [norm_mul,hz,ZMod.stdAddChar_apply,Circle.norm_coe,one_mul] at n
      rw [ite_eq_left h,mul_one]
      rw [ZMod.stdAddChar_apply]
      linarith [(abs_le.mp n).1]
  have e := sum_le_sum (s := S) (fun x hx => sum_le_sum (s := U) (fun y hy => bound x hx y hy))
  simp only [sum_sub_distrib,sum_const,nsmul_eq_mul,← mul_sum] at e
  have hsum : (∑ x ∈ S, ∑ y ∈ U, (z*ZMod.stdAddChar (A x y)).re) ≤
      ‖∑ x ∈ S, ∑ y ∈ U, ZMod.stdAddChar (A x y)‖ := by
    simp_rw [← Complex.re_sum,← mul_sum]
    exact (Complex.re_le_norm _).trans_eq (by rw [norm_mul,hz,one_mul])
  apply le_trans _ (e.trans hsum)
  have id : (∑ x ∈ S, ∑ y ∈ U, if A x y ≠ B x y then (1:ℝ) else 0) =
      errors (fun x y => A x y ≠ B x y) S U := by
    apply sum_congr rfl
    intro x _
    apply sum_congr rfl
    intro y _
    by_cases h : A x y = B x y <;> simp [h]
  rw [id]
  nlinarith only [low]

end InducedDegreeRepetition.Approximation
