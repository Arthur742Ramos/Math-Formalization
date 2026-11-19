module

public import BoundedEdgeRegularSubgraphs.GaussianPolynomialStein
import Mathlib.Tactic

/-!
# The cubic correction and its Gaussian generator
-/

@[expose] public section

open MeasureTheory MvPolynomial Matrix
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

/-- The auxiliary cubic-plus-linear polynomial from Lemma A.2. -/
noncomputable def gaussianCubicAuxiliary {n : ℕ} {ι : Type*}
    (A : Finset ι) (a : ι → ℝ) (v : ι → Fin n → ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ e ∈ A, C (a e) *
    (C (1 / 3 : ℝ) * linearPolynomial (v e) ^ 3 +
      C (2 * ∑ i, v e i ^ 2) * linearPolynomial (v e))

theorem pderiv_gaussianCubicAuxiliary {n : ℕ} {ι : Type*}
    (A : Finset ι) (a : ι → ℝ) (v : ι → Fin n → ℝ) (i : Fin n) :
    pderiv i (gaussianCubicAuxiliary A a v) =
      ∑ e ∈ A, C (a e * v e i) *
        (linearPolynomial (v e) ^ 2 + C (2 * ∑ j, v e j ^ 2)) := by
  simp only [gaussianCubicAuxiliary, map_sum, pderiv_C_mul, map_add, pderiv_pow,
    pderiv_linearPolynomial, Nat.reduceSub]
  apply Finset.sum_congr rfl
  intro e _
  have h : (C (1 / 3 : ℝ) : MvPolynomial (Fin n) ℝ) * ((3 : ℕ) : MvPolynomial (Fin n) ℝ) = 1 := by
    rw [← map_natCast C 3, ← map_mul]
    norm_num
  rw [← mul_assoc (C (1 / 3 : ℝ)) _ _, ← mul_assoc (C (1 / 3 : ℝ)) _ _, h, one_mul]
  simp only [map_mul]
  ring

/-- The auxiliary polynomial has the original cubic as its negative
Gaussian generator. -/
theorem eval_gaussianGeneratorNeg_cubicAuxiliary {n : ℕ} {ι : Type*}
    (A : Finset ι) (a : ι → ℝ) (v : ι → Fin n → ℝ) (x : Fin n → ℝ) :
    eval x (gaussianGeneratorNeg (gaussianCubicAuxiliary A a v)) =
      eval x (gaussianCubicPolynomial A a v) := by
  let Y (e : ι) := v e ⬝ᵥ x
  let c (e : ι) := ∑ i, v e i ^ 2
  let G := gaussianCubicAuxiliary A a v
  have hD (i : Fin n) : eval x (pderiv i G) =
      ∑ e ∈ A, a e * ((Y e ^ 2 + 2 * c e) * v e i) := by
    rw [pderiv_gaussianCubicAuxiliary]
    simp only [map_sum, map_mul, map_pow, map_add, eval_C, eval_linearPolynomial]
    exact Finset.sum_congr rfl (fun e _ ↦ by dsimp only [Y, c]; ring)
  have hDD (i : Fin n) : eval x (pderiv i (pderiv i G)) =
      ∑ e ∈ A, a e * (2 * Y e * v e i ^ 2) := by
    have hterm (e : ι) :
        pderiv i (C (a e * v e i) * (linearPolynomial (v e) ^ 2 + C (2 * ∑ j, v e j ^ 2))) =
          C (a e * v e i) * (2 * linearPolynomial (v e) * C (v e i)) := by
      rw [pderiv_C_mul, map_add, pderiv_C, add_zero, pderiv_pow, pderiv_linearPolynomial]
      norm_num
    rw [pderiv_gaussianCubicAuxiliary, map_sum, map_sum]
    simp_rw [hterm]
    simp only [map_mul, map_ofNat, eval_C, eval_linearPolynomial]
    exact Finset.sum_congr rfl (fun e _ ↦ by dsimp only [Y]; ring)
  change eval x (gaussianGeneratorNeg G) = _
  simp only [gaussianGeneratorNeg, map_sum, map_sub, map_mul, eval_X, hD, hDD,
    eval_gaussianCubicPolynomial]
  simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  have hh (i : Fin n) : x i * (a e * ((Y e ^ 2 + 2 * c e) * v e i)) -
      a e * (2 * Y e * v e i ^ 2) =
      a e * (x i * ((Y e ^ 2 + 2 * c e) * v e i) - 2 * Y e * v e i ^ 2) := by ring
  simp_rw [hh, ← Finset.mul_sum]
  exact congrArg (a e * ·) (gaussian_cubic_generator (v e) x)

/-- The cubic second moment is the expected gradient product in the
characteristic-function equation. -/
theorem integral_gaussianCubic_gradientProduct_eq_secondMoment {n : ℕ} {ι : Type*}
    (A : Finset ι) (a : ι → ℝ) (v : ι → Fin (n + 1) → ℝ) :
    let F := gaussianCubicPolynomial A a v
    let G := gaussianCubicAuxiliary A a v
    let γ := standardGaussianProduct (n + 1)
    (∫ x, eval x (gaussianGradientProduct F G) ∂γ) = ∫ x, eval x F ^ 2 ∂γ := by
  have h := integral_mul_gaussianGeneratorNeg_eq_gradientProduct
    (gaussianCubicPolynomial A a v) (gaussianCubicAuxiliary A a v)
  simpa only [eval_gaussianGeneratorNeg_cubicAuxiliary, ← pow_two] using h.symm

end BoundedEdgeRegularSubgraphs
