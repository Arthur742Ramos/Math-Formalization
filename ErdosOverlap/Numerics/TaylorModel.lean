module

public import ErdosOverlap.Numerics.FourierPolynomial
public import ErdosOverlap.Numerics.FixedTrig
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! # Certified local polynomial approximations of the actual cosine kernel -/

namespace ErdosOverlap.Numerics

open LeanCert.Core Set

@[expose] public section
noncomputable section

def cosineCycle (k : ℕ) : ℝ → ℝ :=
  if k%4=0 then Real.cos else if k%4=1 then fun x => -Real.sin x
  else if k%4=2 then fun x => -Real.cos x else Real.sin

theorem iteratedDeriv_cosine_cycle (k : ℕ) :
    iteratedDeriv k Real.cos = cosineCycle k := by
  induction k with
  | zero => simp [cosineCycle]
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    have h4 : k%4<4 := Nat.mod_lt k (by norm_num)
    rcases (by omega : k%4=0 ∨ k%4=1 ∨ k%4=2 ∨ k%4=3) with h0 | h1 | h2 | h3
    · have hn : (k+1)%4=1 := by omega
      simp [cosineCycle, h0, hn]
    · have hn : (k+1)%4=2 := by omega
      simp [cosineCycle, h1, hn]
    · have hn : (k+1)%4=3 := by omega
      simp [cosineCycle, h2, hn]
    · have hn : (k+1)%4=0 := by omega
      simp [cosineCycle, h3, hn]

def CosineTerm.normalized (a : CosineTerm) (center radius : ℚ) (u : ℝ) : ℝ :=
  (a.weight : ℝ)*Real.cos ((a.frequency : ℝ)*(center : ℝ) +
    ((a.frequency*radius : ℚ) : ℝ)*u)

def CosineTerm.localCoefficient (a : CosineTerm) (center radius : ℚ) (k : ℕ) : ℝ :=
  ((a.weight*(a.frequency*radius)^k/(k.factorial : ℚ) : ℚ) : ℝ)*
    cosineCycle k ((a.frequency*center : ℚ) : ℝ)

def CosineTerm.localPolynomial (a : CosineTerm) (center radius : ℚ) (n : ℕ) (u : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, a.localCoefficient center radius k*u^k

def CosineTerm.remainderBound (a : CosineTerm) (radius : ℚ) (n : ℕ) : ℚ :=
  |a.weight| * |a.frequency*radius|^n/(n.factorial : ℚ)

theorem CosineTerm.normalized_eq_value (a : CosineTerm) (center radius : ℚ) (u : ℝ) :
    a.normalized center radius u = a.value ((center : ℝ)+(radius : ℝ)*u) := by
  unfold CosineTerm.normalized CosineTerm.value
  push_cast
  congr 2
  ring

theorem CosineTerm.normalized_contDiff (a : CosineTerm) (center radius : ℚ) (n : ℕ) :
    ContDiff ℝ n (a.normalized center radius) := by
  unfold CosineTerm.normalized
  fun_prop

theorem CosineTerm.iteratedDeriv_normalized (a : CosineTerm) (center radius : ℚ)
    (n : ℕ) (u : ℝ) :
    iteratedDeriv n (a.normalized center radius) u =
      (a.weight : ℝ)*((a.frequency*radius : ℚ) : ℝ)^n *
        iteratedDeriv n Real.cos
          ((a.frequency : ℝ)*(center : ℝ)+((a.frequency*radius : ℚ) : ℝ)*u) := by
  unfold CosineTerm.normalized
  rw [iteratedDeriv_const_mul_field]
  have hg : ContDiff ℝ n (fun y : ℝ => Real.cos ((a.frequency : ℝ)*(center : ℝ)+y)) := by
    fun_prop
  rw [iteratedDeriv_comp_const_mul hg, iteratedDeriv_comp_const_add]
  ring

theorem CosineTerm.localCoefficient_eq_deriv (a : CosineTerm) (center radius : ℚ) (k : ℕ) :
    a.localCoefficient center radius k = iteratedDeriv k (a.normalized center radius) 0 / k.factorial := by
  rw [a.iteratedDeriv_normalized, iteratedDeriv_cosine_cycle]
  simp only [CosineTerm.localCoefficient, Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_natCast, mul_zero, add_zero]
  ring

theorem CosineTerm.normalized_derivative_bound (a : CosineTerm) (center radius : ℚ)
    (n : ℕ) (u : ℝ) :
    ‖iteratedDeriv n (a.normalized center radius) u‖ ≤
      (|a.weight| : ℚ)*((|a.frequency*radius| : ℚ) : ℝ)^n := by
  rw [a.iteratedDeriv_normalized, norm_mul, norm_mul, Real.norm_eq_abs,
    norm_pow, Real.norm_eq_abs]
  have h := Real.abs_iteratedDeriv_cos_le_one n
    ((a.frequency : ℝ)*(center : ℝ)+((a.frequency*radius : ℚ) : ℝ)*u)
  have hm := mul_le_mul_of_nonneg_left h
    (mul_nonneg (abs_nonneg (a.weight : ℝ))
      (pow_nonneg (abs_nonneg ((a.frequency*radius : ℚ) : ℝ)) n))
  simpa only [Real.norm_eq_abs, Rat.cast_abs, mul_one] using hm

/-- The true function is within the exact rational Taylor remainder on every
point of the normalized cell. -/
theorem CosineTerm.localPolynomial_error (a : CosineTerm) (center radius : ℚ) (n : ℕ)
    {u : ℝ} (hu : |u| ≤ 1) :
    |a.value ((center : ℝ)+(radius : ℝ)*u)-a.localPolynomial center radius n u| ≤
      (a.remainderBound radius n : ℝ) := by
  have hM : 0 ≤ (|a.weight| : ℚ)*((|a.frequency*radius| : ℚ) : ℝ)^n := by positivity
  have h := LeanCert.Core.taylor_remainder_bound
    (a := (-1 : ℝ)) (b := 1) (c := 0) (n := n)
    (by norm_num) (by norm_num) (by norm_num)
    (a.normalized_contDiff center radius n)
    (fun x _ => a.normalized_derivative_bound center radius n x) hM u
    (abs_le.mp hu)
  have hp : |u|^n ≤ (1 : ℝ) := by simpa using pow_le_pow_left₀ (abs_nonneg u) hu n
  have hfac : (0 : ℝ) ≤ n.factorial := Nat.cast_nonneg _
  have hbound := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp hM) hfac
  rw [a.normalized_eq_value] at h
  simp only [sub_zero, Real.norm_eq_abs] at h
  have he : (∑ k ∈ Finset.range n, (iteratedDeriv k (a.normalized center radius) 0 / k.factorial)*u^k) =
      a.localPolynomial center radius n u := by
    apply Finset.sum_congr rfl
    intro k _
    rw [a.localCoefficient_eq_deriv]
  rw [he] at h
  have hh := h.trans hbound
  simpa only [CosineTerm.remainderBound, Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_abs, Rat.cast_natCast, mul_one] using hh

end
end
end ErdosOverlap.Numerics
