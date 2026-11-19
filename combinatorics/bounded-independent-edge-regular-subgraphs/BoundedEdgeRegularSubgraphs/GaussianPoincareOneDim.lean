module

public import BoundedEdgeRegularSubgraphs.GaussianMoments
public import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# The one-dimensional Gaussian Poincaré inequality
-/

public section

open MeasureTheory ProbabilityTheory

namespace BoundedEdgeRegularSubgraphs

private theorem interval_integral_sq_le_length_mul {f : ℝ → ℝ} (hf : Continuous f)
    (a b : ℝ) :
    (∫ x in a..b, f x) ^ 2 ≤ (b - a) * ∫ x in a..b, f x ^ 2 := by
  have hle (u v : ℝ) (huv : u < v) :
      (∫ x in u..v, f x) ^ 2 ≤ (v - u) * ∫ x in u..v, f x ^ 2 := by
    let s := ∫ x in u..v, f x
    let L := v - u
    let c := s / L
    have hL : 0 < L := sub_pos.mpr huv
    have hpt (x : ℝ) : (f x - c) ^ 2 = f x ^ 2 - (2 * c) * f x + c ^ 2 := by ring
    have hi : IntervalIntegrable (fun x ↦ f x ^ 2) volume u v := (hf.pow 2).intervalIntegrable _ _
    have hm : IntervalIntegrable (fun x ↦ (2 * c) * f x) volume u v :=
      (continuous_const.mul hf).intervalIntegrable _ _
    have hk : IntervalIntegrable (fun _ : ℝ ↦ c ^ 2) volume u v :=
      continuous_const.intervalIntegrable _ _
    have hh : 0 ≤ ∫ x in u..v, (f x - c) ^ 2 :=
      intervalIntegral.integral_nonneg_of_forall huv.le (fun _ ↦ sq_nonneg _)
    simp_rw [hpt] at hh
    rw [intervalIntegral.integral_add (hi.sub hm) hk,
      intervalIntegral.integral_sub hi hm, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, smul_eq_mul] at hh
    change 0 ≤ (∫ x in u..v, f x ^ 2) - 2 * c * s + L * c ^ 2 at hh
    have h := mul_nonneg hL.le hh
    have he : L * ((∫ x in u..v, f x ^ 2) - 2 * c * s + L * c ^ 2) =
        L * (∫ x in u..v, f x ^ 2) - s ^ 2 := by
      dsimp only [c]
      field_simp
      ring
    rw [he] at h
    exact sub_nonneg.mp h
  rcases lt_trichotomy a b with hab | hab | hab
  · exact hle a b hab
  · subst b
    simp
  · have h := hle b a hab
    have he₁ : (∫ x in a..b, f x) = -(∫ x in b..a, f x) := intervalIntegral.integral_symm b a
    have he₂ : (∫ x in a..b, f x ^ 2) = -(∫ x in b..a, f x ^ 2) :=
      intervalIntegral.integral_symm b a
    rw [he₁, he₂, neg_sq, mul_neg, ← neg_mul, neg_sub]
    exact h

/-- The one-dimensional Poincaré estimate follows from the interval
Cauchy–Schwarz inequality and Gaussian integration by parts. The function
`G` is the primitive of the squared derivative vanishing at zero. -/
theorem variance_gaussianReal_le_deriv_sq_of_primitive (F D G : ℝ → ℝ)
    (hD : Continuous D) (hF : ∀ x, HasDerivAt F (D x) x)
    (hG : ∀ x, HasDerivAt G (D x ^ 2) x) (hG₀ : G 0 = 0)
    (hF₂ : Integrable (fun x ↦ (F x - F 0) ^ 2) (gaussianReal 0 1))
    (hGint : Integrable G (gaussianReal 0 1))
    (hDint : Integrable (fun x ↦ D x ^ 2) (gaussianReal 0 1))
    (hXint : Integrable (fun x ↦ x * G x) (gaussianReal 0 1)) :
    Var[F; gaussianReal 0 1] ≤ ∫ x, D x ^ 2 ∂gaussianReal 0 1 := by
  have hFp (x : ℝ) : (∫ t in 0..x, D t) = F x - F 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hF t) (hD.intervalIntegrable _ _)
  have hGp (x : ℝ) : (∫ t in 0..x, D t ^ 2) = G x := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hG t)
      ((hD.pow 2).intervalIntegrable _ _), hG₀, sub_zero]
  have hpt (x : ℝ) : (F x - F 0) ^ 2 ≤ x * G x := by
    simpa only [hFp x, hGp x, sub_zero] using interval_integral_sq_le_length_mul hD 0 x
  have hI := integral_mono hF₂ hXint hpt
  have hparts := integral_gaussianReal_deriv_eq_mul G (fun x ↦ D x ^ 2) hG hGint hDint hXint
  have hm : Continuous F := continuous_iff_continuousAt.mpr (fun x ↦ (hF x).continuousAt)
  rw [← variance_sub_const hm.measurable.aestronglyMeasurable (F 0)]
  exact (variance_le_expectation_sq (hm.sub continuous_const).measurable.aestronglyMeasurable).trans
    (hI.trans_eq hparts.symm)

end BoundedEdgeRegularSubgraphs
