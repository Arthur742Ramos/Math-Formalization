/-
Copyright (c) 2026. Released under the BSD-3-Clause license.
-/
module

public import ErdosOverlap.Numerics.TaylorModel

/-! # Certified local polynomial approximations of sine terms -/

namespace ErdosOverlap.Numerics

open LeanCert.Core Set

@[expose] public section
noncomputable section

def sineCycle (k : ℕ) : ℝ → ℝ :=
  if k%4=0 then Real.sin else if k%4=1 then Real.cos
  else if k%4=2 then fun x => -Real.sin x else fun x => -Real.cos x

theorem iteratedDeriv_sine_cycle (k : ℕ) :
    iteratedDeriv k Real.sin = sineCycle k := by
  induction k with
  | zero => simp [sineCycle]
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    have h4 : k%4<4 := Nat.mod_lt k (by norm_num)
    rcases (by omega : k%4=0 ∨ k%4=1 ∨ k%4=2 ∨ k%4=3) with h0 | h1 | h2 | h3
    · have hn : (k+1)%4=1 := by omega
      simp [sineCycle, h0, hn]
    · have hn : (k+1)%4=2 := by omega
      simp [sineCycle, h1, hn]
    · have hn : (k+1)%4=3 := by omega
      simp [sineCycle, h2, hn]
    · have hn : (k+1)%4=0 := by omega
      simp [sineCycle, h3, hn]

def CosineTerm.sineValue (a : CosineTerm) (t : ℝ) : ℝ :=
  (a.weight : ℝ) * Real.sin ((a.frequency : ℝ) * t)

def CosineTerm.sineNormalized (a : CosineTerm) (center radius : ℚ) (u : ℝ) : ℝ :=
  (a.weight : ℝ)*Real.sin ((a.frequency : ℝ)*(center : ℝ) +
    ((a.frequency*radius : ℚ) : ℝ)*u)

def CosineTerm.sineCoefficient (a : CosineTerm) (center radius : ℚ) (k : ℕ) : ℝ :=
  ((a.weight*(a.frequency*radius)^k/(k.factorial : ℚ) : ℚ) : ℝ)*
    sineCycle k ((a.frequency*center : ℚ) : ℝ)

def CosineTerm.sinePolynomial (a : CosineTerm) (center radius : ℚ) (n : ℕ) (u : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, a.sineCoefficient center radius k*u^k

theorem CosineTerm.sineNormalized_eq_value (a : CosineTerm) (center radius : ℚ) (u : ℝ) :
    a.sineNormalized center radius u = a.sineValue ((center : ℝ)+(radius : ℝ)*u) := by
  unfold CosineTerm.sineNormalized CosineTerm.sineValue
  push_cast
  congr 2
  ring

theorem CosineTerm.sineNormalized_contDiff (a : CosineTerm) (center radius : ℚ) (n : ℕ) :
    ContDiff ℝ n (a.sineNormalized center radius) := by
  unfold CosineTerm.sineNormalized
  fun_prop

theorem CosineTerm.iteratedDeriv_sineNormalized (a : CosineTerm) (center radius : ℚ)
    (n : ℕ) (u : ℝ) :
    iteratedDeriv n (a.sineNormalized center radius) u =
      (a.weight : ℝ)*((a.frequency*radius : ℚ) : ℝ)^n *
        iteratedDeriv n Real.sin
          ((a.frequency : ℝ)*(center : ℝ)+((a.frequency*radius : ℚ) : ℝ)*u) := by
  unfold CosineTerm.sineNormalized
  rw [iteratedDeriv_const_mul_field]
  have hg : ContDiff ℝ n (fun y : ℝ => Real.sin ((a.frequency : ℝ)*(center : ℝ)+y)) := by
    fun_prop
  rw [iteratedDeriv_comp_const_mul hg, iteratedDeriv_comp_const_add]
  ring

theorem CosineTerm.sineCoefficient_eq_deriv (a : CosineTerm) (center radius : ℚ) (k : ℕ) :
    a.sineCoefficient center radius k = iteratedDeriv k (a.sineNormalized center radius) 0 / k.factorial := by
  rw [a.iteratedDeriv_sineNormalized, iteratedDeriv_sine_cycle]
  simp only [CosineTerm.sineCoefficient, Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_natCast, mul_zero, add_zero]
  ring

theorem CosineTerm.sineNormalized_derivative_bound (a : CosineTerm) (center radius : ℚ)
    (n : ℕ) (u : ℝ) :
    ‖iteratedDeriv n (a.sineNormalized center radius) u‖ ≤
      (|a.weight| : ℚ)*((|a.frequency*radius| : ℚ) : ℝ)^n := by
  rw [a.iteratedDeriv_sineNormalized, norm_mul, norm_mul, Real.norm_eq_abs,
    norm_pow, Real.norm_eq_abs]
  have h : |iteratedDeriv n Real.sin
      ((a.frequency : ℝ)*(center : ℝ)+((a.frequency*radius : ℚ) : ℝ)*u)| ≤ 1 := by
    rw [iteratedDeriv_sine_cycle]
    unfold sineCycle
    split_ifs
    all_goals first
      | exact Real.abs_sin_le_one _
      | exact Real.abs_cos_le_one _
      | simpa only [abs_neg] using Real.abs_sin_le_one _
      | simpa only [abs_neg] using Real.abs_cos_le_one _
  have hm := mul_le_mul_of_nonneg_left h
    (mul_nonneg (abs_nonneg (a.weight : ℝ))
      (pow_nonneg (abs_nonneg ((a.frequency*radius : ℚ) : ℝ)) n))
  simpa only [Real.norm_eq_abs, Rat.cast_abs, mul_one] using hm

/-- The true function is within the exact rational Taylor remainder on every
point of the normalized cell. -/
theorem CosineTerm.sinePolynomial_error (a : CosineTerm) (center radius : ℚ) (n : ℕ)
    {u : ℝ} (hu : |u| ≤ 1) :
    |a.sineValue ((center : ℝ)+(radius : ℝ)*u)-a.sinePolynomial center radius n u| ≤
      (a.remainderBound radius n : ℝ) := by
  have hM : 0 ≤ (|a.weight| : ℚ)*((|a.frequency*radius| : ℚ) : ℝ)^n := by positivity
  have h := LeanCert.Core.taylor_remainder_bound
    (a := (-1 : ℝ)) (b := 1) (c := 0) (n := n)
    (by norm_num) (by norm_num) (by norm_num)
    (a.sineNormalized_contDiff center radius n)
    (fun x _ => a.sineNormalized_derivative_bound center radius n x) hM u
    (abs_le.mp hu)
  have hp : |u|^n ≤ (1 : ℝ) := by simpa using pow_le_pow_left₀ (abs_nonneg u) hu n
  have hfac : (0 : ℝ) ≤ n.factorial := Nat.cast_nonneg _
  have hbound := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp hM) hfac
  rw [a.sineNormalized_eq_value] at h
  simp only [sub_zero, Real.norm_eq_abs] at h
  have he : (∑ k ∈ Finset.range n, (iteratedDeriv k (a.sineNormalized center radius) 0 / k.factorial)*u^k) =
      a.sinePolynomial center radius n u := by
    apply Finset.sum_congr rfl
    intro k _
    rw [a.sineCoefficient_eq_deriv]
  rw [he] at h
  have hh := h.trans hbound
  simpa only [CosineTerm.remainderBound, Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_abs, Rat.cast_natCast, mul_one] using hh

end
end
end ErdosOverlap.Numerics
