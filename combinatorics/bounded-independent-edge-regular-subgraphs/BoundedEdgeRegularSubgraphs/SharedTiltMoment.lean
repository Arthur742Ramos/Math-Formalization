module

public import BoundedEdgeRegularSubgraphs.TiltDerivative
public import BoundedEdgeRegularSubgraphs.Fourier
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

/-!
# Shared-edge likelihood products
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

private theorem hasDerivAt_logTiltNormalizer (q : Icc (0 : ℝ) 1) (u : ℝ) :
    HasDerivAt (fun x ↦ Real.log (tiltNormalizer q x)) (tiltProb q u : ℝ) u := by
  have h : HasDerivAt (tiltNormalizer q) ((q : ℝ) * Real.exp u) u := by
    unfold tiltNormalizer
    exact ((Real.hasDerivAt_exp u).const_mul (q : ℝ)).const_add (1 - (q : ℝ))
  simpa only [tiltProb] using h.log (tiltNormalizer_pos q u).ne'

/-- A double difference of the log normalizing constant is bounded by
the two log-odds shifts and the Bernoulli variance upper bound. -/
theorem abs_logTiltNormalizer_double_sub_le (q : Icc (0 : ℝ) 1) (s t : ℝ) :
    |Real.log (tiltNormalizer q (s + t)) - Real.log (tiltNormalizer q s) -
      Real.log (tiltNormalizer q t)| ≤ (s ^ 2 + t ^ 2) / 8 := by
  let f (u : ℝ) := Real.log (tiltNormalizer q (u + t)) - Real.log (tiltNormalizer q u)
  have hd (u : ℝ) : HasDerivAt f ((tiltProb q (u + t) : ℝ) - tiltProb q u) u := by
    have h := (hasDerivAt_logTiltNormalizer q (u + t)).comp u ((hasDerivAt_id u).add_const t)
    simp only [id_eq, mul_one, Function.comp_def] at h
    exact h.sub (hasDerivAt_logTiltNormalizer q u)
  have hconst (u : ℝ) : ‖(tiltProb q (u + t) : ℝ) - tiltProb q u‖ ≤ |t| / 4 := by
    rw [Real.norm_eq_abs]
    have h := abs_tiltProb_sub_le q (u + t) u
    rw [show u + t - u = t by ring] at h
    linarith only [h]
  have ha := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x (_ : x ∈ (univ : Set ℝ)) ↦ (hd x).hasDerivWithinAt)
    (fun x _ ↦ hconst x) (mem_univ (0 : ℝ)) (mem_univ s)
  have hf : f 0 = Real.log (tiltNormalizer q t) := by simp [f, tiltNormalizer]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero, hf] at ha
  have hst := sq_nonneg (|s| - |t|)
  rw [sub_sq, sq_abs, sq_abs] at hst
  exact ha.trans (by nlinarith only [hst])

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- Under the original edge law the expected product of two likelihood
factors on a shared edge set is bounded by the squared shifts. -/
theorem integral_shared_tilt_likelihood_product_le
    (A : Finset (Edge α)) (q : Edge α → Icc (0 : ℝ) 1) (s t : Edge α → ℝ) :
    (∫ w, (∏ e ∈ A, Real.exp (s e * w e) / tiltNormalizer (q e) (s e)) *
      (∏ e ∈ A, Real.exp (t e * w e) / tiltNormalizer (q e) (t e)) ∂graphLaw q) ≤
      Real.exp (∑ e ∈ A, (s e ^ 2 + t e ^ 2) / 8) := by
  classical
  let f (e : Edge α) (w : ℝ) :=
    if e ∈ A then Real.exp ((s e + t e) * w) /
      (tiltNormalizer (q e) (s e) * tiltNormalizer (q e) (t e)) else 1
  have hfun (w : Edge α → ℝ) : (∏ e ∈ A, Real.exp (s e * w e) / tiltNormalizer (q e) (s e)) *
      (∏ e ∈ A, Real.exp (t e * w e) / tiltNormalizer (q e) (t e)) = ∏ e, f e (w e) := by
    rw [← Finset.prod_mul_distrib]
    simp only [f, ← Finset.prod_filter]
    rw [show Finset.univ.filter (fun e ↦ e ∈ A) = A by ext; simp]
    apply Finset.prod_congr rfl
    intro e _
    rw [div_mul_div_comm, ← Real.exp_add, add_mul]
  simp_rw [hfun]
  rw [graphLaw, integral_fintype_prod_eq_prod f]
  have hi (e : Edge α) :
      (∫ w, f e w ∂bernoulliMeasure (1 : ℝ) 0 (q e)) =
        if e ∈ A then Real.exp (Real.log (tiltNormalizer (q e) (s e + t e)) -
          Real.log (tiltNormalizer (q e) (s e)) - Real.log (tiltNormalizer (q e) (t e))) else 1 := by
    rw [integral_bernoulliMeasure]
    by_cases he : e ∈ A
    · simp only [f, if_pos he, mul_one, mul_zero, Real.exp_zero, smul_eq_mul, Real.exp_sub,
        Real.exp_log (tiltNormalizer_pos _ _)]
      unfold tiltNormalizer
      field_simp
      <;> ring
    · simp only [f, if_neg he, smul_eq_mul, mul_one]
      ring
  simp_rw [hi]
  rw [← Finset.prod_filter, show Finset.univ.filter (fun e ↦ e ∈ A) = A by ext; simp, ← Real.exp_sum]
  apply Real.exp_le_exp.mpr
  exact Finset.sum_le_sum (fun e _ ↦ (le_abs_self _).trans (abs_logTiltNormalizer_double_sub_le (q e) _ _))

end BoundedEdgeRegularSubgraphs
