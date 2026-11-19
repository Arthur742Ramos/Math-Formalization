module

public import BoundedEdgeRegularSubgraphs.GaussianCubicMoment
public import BoundedEdgeRegularSubgraphs.GaussianStein
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Tactic

/-!
# The polynomial Gaussian integration-by-parts identities
-/

@[expose] public section

open MeasureTheory MvPolynomial Matrix
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

/-- The negative Ornstein–Uhlenbeck generator on polynomials. -/
noncomputable def gaussianGeneratorNeg {n : ℕ} (g : MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  ∑ i, (X i * pderiv i g - pderiv i (pderiv i g))

/-- The scalar product of the two polynomial gradients. -/
noncomputable def gaussianGradientProduct {n : ℕ} (f g : MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  ∑ i, pderiv i f * pderiv i g

private theorem hasDerivAt_eval_insertNth {n : ℕ} (p : MvPolynomial (Fin (n + 1)) ℝ)
    (i : Fin (n + 1)) (y : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun s ↦ eval (i.insertNth s y) p) (eval (i.insertNth t y) (pderiv i p)) t := by
  let ins (s : ℝ) : Fin (n + 1) → ℝ := i.insertNth s y
  have heq (s : ℝ) : Function.update (ins 0) i s = ins s := by
    apply funext
    apply (i.forall_iff_succAbove (P := fun j ↦
      Function.update (ins 0) i s j = ins s j)).mpr
    constructor
    · simp only [ins, Function.update_self, Fin.insertNth_apply_same]
    · intro k
      rw [Function.update_of_ne (Fin.succAbove_ne _ _)]
      simp only [ins, Fin.insertNth_apply_succAbove]
  change HasDerivAt (fun s ↦ eval (ins s) p) (eval (ins t) (pderiv i p)) t
  simpa only [heq] using hasDerivAt_eval_coordinate p (ins 0) i t

/-- Testing by the polynomial itself gives the equality of the second
moment and the expected gradient product used in Lemma A.2. -/
theorem integral_mul_gaussianGeneratorNeg_eq_gradientProduct {n : ℕ}
    (f g : MvPolynomial (Fin (n + 1)) ℝ) :
    let γ := standardGaussianProduct (n + 1)
    (∫ x, eval x f * eval x (gaussianGeneratorNeg g) ∂γ) =
      ∫ x, eval x (gaussianGradientProduct f g) ∂γ := by
  let γ := standardGaussianProduct (n + 1)
  have h := gaussianProduct_stein_identity (fun x ↦ eval x f)
    (fun i x ↦ eval x (pderiv i f)) (fun i x ↦ eval x (pderiv i g))
    (fun i x ↦ eval x (pderiv i (pderiv i g))) id (fun _ ↦ 1)
    hasDerivAt_id (hasDerivAt_eval_insertNth f) (fun i ↦ hasDerivAt_eval_insertNth (pderiv i g) i)
    (fun i ↦ by
      simpa only [map_mul, id_eq] using integrable_eval_standardGaussianProduct (f * pderiv i g))
    (fun i ↦ by
      have he (x : Fin (n + 1) → ℝ) :
          eval x (X i * (f * pderiv i g)) = x i * (eval x f * eval x (pderiv i g)) := by
        rw [map_mul, eval_X, map_mul]
      change Integrable (fun x ↦ x i * (eval x f * eval x (pderiv i g))) γ
      rw [← funext he]
      exact integrable_eval_standardGaussianProduct (X i * (f * pderiv i g)))
    (fun i ↦ by
      simpa only [map_mul, id_eq] using
        integrable_eval_standardGaussianProduct (f * pderiv i (pderiv i g)))
    (fun i ↦ by
      simpa only [map_mul, one_mul] using
        integrable_eval_standardGaussianProduct (pderiv i f * pderiv i g))
  simpa only [gaussianGeneratorNeg, gaussianGradientProduct, map_sum, map_sub, map_mul,
    eval_X, id_eq, one_mul] using h

/-- A bounded test function with bounded derivative satisfies the Stein
identity for the polynomial pair. -/
theorem integral_gaussianGeneratorNeg_mul_test_eq {n : ℕ}
    (f g : MvPolynomial (Fin (n + 1)) ℝ) (b b' : ℝ → ℝ) {M N : ℝ}
    (hb : ∀ t, HasDerivAt b (b' t) t) (hb' : Measurable b')
    (hM : ∀ t, |b t| ≤ M) (hN : ∀ t, |b' t| ≤ N) :
    let γ := standardGaussianProduct (n + 1)
    (∫ x, b (eval x f) * eval x (gaussianGeneratorNeg g) ∂γ) =
      ∫ x, b' (eval x f) * eval x (gaussianGradientProduct f g) ∂γ := by
  let γ := standardGaussianProduct (n + 1)
  have hbi : Measurable b := (continuous_iff_continuousAt.mpr
    (fun t ↦ (hb t).continuousAt)).measurable
  have hbInt (c : ℝ → ℝ) (hc : Measurable c) {K : ℝ} (hK : ∀ t, |c t| ≤ K)
      (p : MvPolynomial (Fin (n + 1)) ℝ) :
      Integrable (fun x ↦ c (eval x f) * eval x p) γ := by
    refine ((integrable_eval_standardGaussianProduct p).abs.const_mul K).mono'
      ((hc.comp f.continuous_eval.measurable).mul p.continuous_eval.measurable).aestronglyMeasurable ?_
    exact ae_of_all _ (fun x ↦ by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hK _) (abs_nonneg _))
  have h := gaussianProduct_stein_identity (fun x ↦ eval x f)
    (fun i x ↦ eval x (pderiv i f)) (fun i x ↦ eval x (pderiv i g))
    (fun i x ↦ eval x (pderiv i (pderiv i g))) b b' hb
    (hasDerivAt_eval_insertNth f) (fun i ↦ hasDerivAt_eval_insertNth (pderiv i g) i)
    (fun i ↦ hbInt b hbi hM (pderiv i g))
    (fun i ↦ by
      have h := hbInt b hbi hM (X i * pderiv i g)
      have he (x : Fin (n + 1) → ℝ) :
          b (eval x f) * eval x (X i * pderiv i g) = x i * (b (eval x f) * eval x (pderiv i g)) := by
        simp only [map_mul, eval_X]
        ring
      simpa only [he] using h)
    (fun i ↦ hbInt b hbi hM (pderiv i (pderiv i g)))
    (fun i ↦ by
      simpa only [map_mul, mul_assoc] using hbInt b' hb' hN (pderiv i f * pderiv i g))
  simpa only [gaussianGeneratorNeg, gaussianGradientProduct, map_sum, map_sub, map_mul,
    eval_X] using h

end BoundedEdgeRegularSubgraphs
