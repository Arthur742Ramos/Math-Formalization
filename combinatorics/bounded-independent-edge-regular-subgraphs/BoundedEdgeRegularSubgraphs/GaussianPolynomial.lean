module

public import BoundedEdgeRegularSubgraphs.GaussianPoincareOneDim
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic

/-!
# Gaussian integrability and Poincaré for real polynomials
-/

public section

open MeasureTheory ProbabilityTheory Polynomial
open scoped BigOperators NNReal

namespace BoundedEdgeRegularSubgraphs

private theorem integrable_pow_gaussianReal (m : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ m) (gaussianReal 0 1) := by
  have hm : MemLp (id : ℝ → ℝ) (m : ENNReal) (gaussianReal 0 1) :=
    memLp_id_gaussianReal' (μ := 0) (v := 1) _ (by simp)
  have h := hm.integrable_norm_pow'
  refine h.mono' ((continuous_id.pow m).measurable.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [id_eq, Real.norm_eq_abs, abs_pow, le_rfl]

theorem integrable_polynomial_gaussianReal (p : ℝ[X]) :
    Integrable p.eval (gaussianReal 0 1) := by
  have he (x : ℝ) : p.eval x = ∑ i ∈ p.support, p.coeff i * x ^ i := by
    rw [Polynomial.eval_eq_sum]
    rfl
  simp_rw [he]
  exact integrable_finsetSum _ (fun i _ ↦ (integrable_pow_gaussianReal i).const_mul _)

/-- The sharp one-dimensional Gaussian Poincaré inequality for polynomials. -/
theorem variance_polynomial_gaussianReal_le (p : ℝ[X]) :
    Var[p.eval; gaussianReal 0 1] ≤ ∫ x, (p.derivative.eval x) ^ 2 ∂gaussianReal 0 1 := by
  let q := p.derivative ^ 2
  let G : ℝ[X] := ∑ i ∈ q.support, Polynomial.C (q.coeff i / ((i : ℝ) + 1)) * Polynomial.X ^ (i + 1)
  have hGe (x : ℝ) : G.eval x = ∑ i ∈ q.support, (q.coeff i / ((i : ℝ) + 1)) * x ^ (i + 1) := by
    simp only [G, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
  have hG₀ : G.eval 0 = 0 := by rw [hGe]; simp
  have hG (x : ℝ) : HasDerivAt G.eval (p.derivative.eval x ^ 2) x := by
    have hd (i : ℕ) :
        HasDerivAt (fun y : ℝ ↦ (q.coeff i / ((i : ℝ) + 1)) * y ^ (i + 1))
          (q.coeff i * x ^ i) x := by
      have h := (hasDerivAt_pow (i + 1) x).const_mul (q.coeff i / ((i : ℝ) + 1))
      have he : (q.coeff i / ((i : ℝ) + 1)) * (((i + 1 : ℕ) : ℝ) * x ^ (i + 1 - 1)) =
          q.coeff i * x ^ i := by
        simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
        field_simp
      simpa only [he] using h
    have hh := HasDerivAt.fun_sum (u := q.support) (fun i _ ↦ hd i)
    have hsum : (∑ i ∈ q.support, q.coeff i * x ^ i) = p.derivative.eval x ^ 2 := by
      change (q.sum fun i a ↦ a * x ^ i) = _
      rw [← Polynomial.eval_eq_sum, Polynomial.eval_pow]
    rwa [← hsum, show G.eval = (fun y ↦ ∑ i ∈ q.support,
      (q.coeff i / ((i : ℝ) + 1)) * y ^ (i + 1)) by funext y; exact hGe y]
  apply variance_gaussianReal_le_deriv_sq_of_primitive p.eval p.derivative.eval G.eval
    p.derivative.continuous (fun x ↦ p.hasDerivAt x) hG hG₀
  · have h := integrable_polynomial_gaussianReal ((p - Polynomial.C (p.eval 0)) ^ 2)
    simpa only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_C] using h
  · exact integrable_polynomial_gaussianReal G
  · have h := integrable_polynomial_gaussianReal q
    change Integrable (fun x ↦ q.eval x) (gaussianReal 0 1) at h
    simpa only [q, Polynomial.eval_pow] using h
  · have h := integrable_polynomial_gaussianReal (Polynomial.X * G)
    change Integrable (fun x ↦ (Polynomial.X * G).eval x) (gaussianReal 0 1) at h
    simpa only [Polynomial.eval_mul, Polynomial.eval_X] using h

end BoundedEdgeRegularSubgraphs
