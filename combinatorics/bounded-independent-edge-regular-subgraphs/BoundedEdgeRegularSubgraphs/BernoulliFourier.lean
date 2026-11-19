module

public import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The modulus of a Bernoulli Fourier factor

These scalar estimates are used in the one-dimensional atom bound and
in the Fourier tail argument of Appendix B.
-/

@[expose] public section

namespace BoundedEdgeRegularSubgraphs

/-- One Fourier factor for a Bernoulli indicator with success probability q. -/
noncomputable def bernoulliFourierFactor (q s : ℝ) : ℂ :=
  1 - (q : ℂ) + (q : ℂ) * Complex.exp ((s : ℂ) * Complex.I)

/-- Exact squared modulus of the Bernoulli factor. -/
theorem bernoulliFourierFactor_norm_sq (q s : ℝ) :
    ‖bernoulliFourierFactor q s‖ ^ 2 =
      1 - 4 * q * (1 - q) * Real.sin (s / 2) ^ 2 := by
  have hcos : Real.cos s = 1 - 2 * Real.sin (s / 2) ^ 2 := by
    calc
      Real.cos s = Real.cos (2 * (s / 2)) := by congr 1; ring
      _ = _ := Real.cos_two_mul_eq_one_sub _
  rw [Complex.sq_norm, Complex.normSq_apply, bernoulliFourierFactor]
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.one_re,
    Complex.ofReal_im, Complex.add_im, Complex.sub_im, Complex.mul_im,
    Complex.one_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, zero_mul,
    sub_zero, add_zero, zero_add]
  calc
    _ = (1 - q) ^ 2 + 2 * (1 - q) * q * Real.cos s +
          q ^ 2 * (Real.sin s ^ 2 + Real.cos s ^ 2) := by ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq, hcos]; ring

/-- Exponential upper bound for the modulus of one edge factor. -/
theorem bernoulliFourierFactor_norm_le (q s : ℝ) :
    ‖bernoulliFourierFactor q s‖ ≤
      Real.exp (-2 * q * (1 - q) * Real.sin (s / 2) ^ 2) := by
  let a := q * (1 - q) * Real.sin (s / 2) ^ 2
  have he : Real.exp (-2 * a) ^ 2 = Real.exp (-(4 * a)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsq : ‖bernoulliFourierFactor q s‖ ^ 2 ≤ Real.exp (-2 * a) ^ 2 := by
    rw [he, bernoulliFourierFactor_norm_sq]
    have hx : 4 * a = 4 * q * (1 - q) * Real.sin (s / 2) ^ 2 := by
      dsimp [a]
      ring
    rw [← hx]
    exact Real.one_sub_le_exp_neg _
  have hform : -2 * a = -2 * q * (1 - q) * Real.sin (s / 2) ^ 2 := by
    dsimp [a]
    ring
  rw [← hform]
  exact (sq_le_sq₀ (norm_nonneg _) (Real.exp_pos _).le).mp hsq

end BoundedEdgeRegularSubgraphs
