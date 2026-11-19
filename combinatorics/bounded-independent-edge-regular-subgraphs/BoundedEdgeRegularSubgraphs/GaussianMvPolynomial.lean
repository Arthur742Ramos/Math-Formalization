module

public import BoundedEdgeRegularSubgraphs.GaussianTensorization
public import BoundedEdgeRegularSubgraphs.GaussianPolynomial
public import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Tactic

/-!
# Gaussian Poincaré for multivariate polynomials
-/

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

theorem integrable_eval_standardGaussianProduct {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    Integrable (fun x ↦ MvPolynomial.eval x p) (standardGaussianProduct n) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial a c =>
    have h (x : Fin n → ℝ) : MvPolynomial.eval x (MvPolynomial.monomial a c) =
        c * ∏ i, x i ^ a i := by
      rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype]
      exact fun _ ↦ pow_zero _
    simp_rw [h]
    exact (Integrable.fintype_prod (μ := fun _ ↦ gaussianReal 0 1)
      (f := fun i (x : ℝ) ↦ x ^ a i) (fun i ↦ integrable_pow_gaussianReal (a i))).const_mul c
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq

theorem hasDerivAt_eval_coordinate {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    HasDerivAt (fun u ↦ MvPolynomial.eval (Function.update x i u) p)
      (MvPolynomial.eval (Function.update x i t) (MvPolynomial.pderiv i p)) t := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.eval_C, MvPolynomial.pderiv_C, map_zero]
    exact hasDerivAt_const t a
  | add p q hp hq =>
    simp only [map_add]
    exact hp.fun_add hq
  | mul_X p j hp =>
    simp only [map_mul, MvPolynomial.eval_X, MvPolynomial.pderiv_mul, map_add]
    by_cases h : j = i
    · subst j
      simp only [Function.update_self, MvPolynomial.pderiv_X_self, map_one, mul_one]
      have hh := hp.fun_mul (hasDerivAt_id t)
      simpa only [id_eq, mul_one] using hh
    · simp only [Function.update_of_ne h, MvPolynomial.pderiv_X_of_ne h, map_zero,
        mul_zero, add_zero]
      have hh := hp.fun_mul (hasDerivAt_const t (x j))
      simpa only [mul_zero, add_zero, zero_add] using hh

private theorem variance_eval_coordinate_le {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ) (i : Fin n) :
    Var[(fun t ↦ MvPolynomial.eval (Function.update x i t) p); gaussianReal 0 1] ≤
      ∫ t, (MvPolynomial.eval (Function.update x i t) (MvPolynomial.pderiv i p)) ^ 2
        ∂gaussianReal 0 1 := by
  classical
  let g (j : Fin n) : Polynomial ℝ := if j = i then Polynomial.X else Polynomial.C (x j)
  let G : Polynomial ℝ := MvPolynomial.eval₂Hom Polynomial.C g p
  have hh (t : ℝ) : G.eval t = MvPolynomial.eval (Function.update x i t) p := by
    let l := (Polynomial.evalRingHom t).comp (MvPolynomial.eval₂Hom Polynomial.C g)
    let r := MvPolynomial.eval (Function.update x i t)
    have h : l = r := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp only [l, r, RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.eval_C]
        exact Polynomial.eval_C
      · intro j
        simp only [l, r, RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.eval_X]
        change (g j).eval t = Function.update x i t j
        dsimp only [g]
        by_cases h : j = i
        · subst j
          simp
        · simp [h, Function.update_of_ne]
    exact DFunLike.congr_fun h p
  have hf : G.eval = fun t ↦ MvPolynomial.eval (Function.update x i t) p := funext hh
  have hd (t : ℝ) : G.derivative.eval t =
      MvPolynomial.eval (Function.update x i t) (MvPolynomial.pderiv i p) := by
    have h := G.hasDerivAt t
    change HasDerivAt G.eval (G.derivative.eval t) t at h
    rw [hf] at h
    exact h.unique (hasDerivAt_eval_coordinate p x i t)
  have h := variance_polynomial_gaussianReal_le G
  rw [hf] at h
  simpa only [hd] using h

/-- The polynomial Poincaré inequality in (A.1), for standard independent
Gaussian coordinates and the usual partial derivatives. -/
theorem variance_mvPolynomial_standardGaussianProduct_le {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    Var[(fun x ↦ MvPolynomial.eval x p); standardGaussianProduct n] ≤
      ∑ i, ∫ x, (MvPolynomial.eval x (MvPolynomial.pderiv i p)) ^ 2 ∂standardGaussianProduct n := by
  apply variance_standardGaussianProduct_le_sum_of_slices
  · apply (memLp_two_iff_integrable_sq
      p.continuous_eval.measurable.aestronglyMeasurable).2
    have h : (fun x : Fin n → ℝ ↦ MvPolynomial.eval x (p ^ 2)) =
        (fun x ↦ MvPolynomial.eval x p ^ 2) := funext (fun x ↦ map_pow (MvPolynomial.eval x) p 2)
    change Integrable (fun x ↦ MvPolynomial.eval x p ^ 2) (standardGaussianProduct n)
    rw [← h]
    exact integrable_eval_standardGaussianProduct (p ^ 2)
  · intro i
    let D := MvPolynomial.pderiv i p
    have h : (fun x : Fin n → ℝ ↦ MvPolynomial.eval x (D ^ 2)) =
        (fun x ↦ MvPolynomial.eval x D ^ 2) := funext (fun x ↦ map_pow (MvPolynomial.eval x) D 2)
    change Integrable (fun x ↦ MvPolynomial.eval x D ^ 2) (standardGaussianProduct n)
    rw [← h]
    exact integrable_eval_standardGaussianProduct (D ^ 2)
  · intro i x
    exact variance_eval_coordinate_le p x i

end BoundedEdgeRegularSubgraphs
