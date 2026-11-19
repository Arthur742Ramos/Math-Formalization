module

public import BoundedEdgeRegularSubgraphs.BernoulliLogExpansion
public import BoundedEdgeRegularSubgraphs.FourierReplacement
import BoundedEdgeRegularSubgraphs.MeanDrift
import Mathlib.Tactic

/-!
# The local expansion of a centred degree Fourier integrand
-/

@[expose] public section

open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

private theorem fourier_integer_coe (n : ℤ) (s : ℝ) :
    fourier n (s : PhaseCircle) = Complex.exp ((n : ℂ) * (s : ℂ) * Complex.I) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

theorem edgeLogFactor_ne_zero (q : Set.Icc (0 : ℝ) 1) (s : ℝ) (hs : |s| ≤ 1 / 4) :
    1 - ((q : ℝ) : ℂ) + ((q : ℝ) : ℂ) * Complex.exp ((s : ℂ) * Complex.I) ≠ 0 := by
  let z := (s : ℂ) * Complex.I
  have hz : ‖z‖ = |s| := by dsimp only [z]; rw [Complex.norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hu : ‖((q : ℝ) : ℂ) * (Complex.exp z - 1)‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg q.property.1]
    have h := mul_le_of_le_one_left (norm_nonneg (Complex.exp z - 1)) q.property.2
    have hE := Complex.norm_exp_sub_one_le (show ‖z‖ ≤ 1 by rw [hz]; linarith)
    rw [hz] at hE
    linarith only [h, hE, hs]
  have he : 1 - ((q : ℝ) : ℂ) + ((q : ℝ) : ℂ) * Complex.exp z =
      1 + ((q : ℝ) : ℂ) * (Complex.exp z - 1) := by ring
  rw [he]
  exact Complex.slitPlane_ne_zero (Complex.mem_slitPlane_of_norm_lt_one hu)

/-- The explicit quadratic, cubic and quartic terms on the imaginary axis. -/
theorem bernoulliCumulantPolynomial_imaginary (q s : ℝ) :
    bernoulliCumulantPolynomial (q : ℂ) ((s : ℂ) * Complex.I) -
      (q : ℂ) * ((s : ℂ) * Complex.I) =
        -(q : ℂ) * (1 - q) * (s : ℂ) ^ 2 / 2 -
          Complex.I * (q : ℂ) * (1 - q) * (1 - 2 * q) * (s : ℂ) ^ 3 / 6 +
          (q : ℂ) * (1 - q) * (1 - 6 * (q : ℂ) * (1 - q)) * (s : ℂ) ^ 4 / 24 := by
  have hI₃ : Complex.I ^ 3 = -Complex.I := by
    rw [pow_succ, Complex.I_sq, neg_one_mul]
  have hI₄ : Complex.I ^ 4 = 1 := by
    rw [pow_succ, hI₃, neg_mul, ← pow_two, Complex.I_sq, neg_neg]
  unfold bernoulliCumulantPolynomial
  rw [mul_pow, mul_pow, mul_pow, Complex.I_sq, hI₃, hI₄]
  ring

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- The local Fourier integrand has the sum of the edge cumulants in its exponent,
with the degree character contributing the linear terms. -/
theorem degreeFourier_eq_exp_log_sum (A : Finset (Edge α))
    (q : Edge α → Set.Icc (0 : ℝ) 1) (d : α → ℤ) (t : α → ℝ)
    (ht : ∀ e ∈ A, |t e.val.1 + t e.val.2| ≤ 1 / 4) :
    degreeFourier A q d (fun i ↦ (t i : PhaseCircle)) =
      Complex.exp (-(∑ i, (d i : ℂ) * (t i : ℂ) * Complex.I) +
        ∑ e ∈ A, Complex.log (1 - ((q e : ℝ) : ℂ) + ((q e : ℝ) : ℂ) *
          Complex.exp (((t e.val.1 + t e.val.2 : ℝ) : ℂ) * Complex.I))) := by
  rw [degreeFourier, Complex.exp_add]
  congr 1
  · unfold latticeCharacter
    simp_rw [fourier_integer_coe, Pi.neg_apply, Int.cast_neg, neg_mul]
    rw [← Complex.exp_sum, Finset.sum_neg_distrib]
  · rw [Complex.exp_sum]
    apply Finset.prod_congr rfl
    intro e he
    rw [Complex.exp_log (edgeLogFactor_ne_zero (q e) _ (ht e he))]
    unfold edgeCharacter
    rw [fourier_one_coe, fourier_one_coe, ← Complex.exp_add]
    have h : (t e.val.1 : ℂ) * Complex.I + (t e.val.2 : ℂ) * Complex.I =
        (((t e.val.1 + t e.val.2 : ℝ) : ℂ) * Complex.I) := by push_cast; ring
    rw [h]

/-- On a centred full degree atom the linear terms cancel exactly. The remaining
error is bounded by a uniform constant times the sum of fifth powers. -/
theorem degreeFourier_full_centered_expansion :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : Edge α → Set.Icc (0 : ℝ) 1) (d : α → ℤ) (t : α → ℝ),
      (∀ i, (d i : ℝ) = degreeSum (fun e ↦ (q e : ℝ)) i) →
      (∀ e : Edge α, |t e.val.1 + t e.val.2| ≤ 1 / 4) →
      ∃ R : ℂ, ‖R‖ ≤ C * ∑ e : Edge α, |t e.val.1 + t e.val.2| ^ 5 ∧
        degreeFourier Finset.univ q d (fun i ↦ (t i : PhaseCircle)) =
          Complex.exp ((∑ e : Edge α,
            (bernoulliCumulantPolynomial ((q e : ℝ) : ℂ)
              (((t e.val.1 + t e.val.2 : ℝ) : ℂ) * Complex.I) -
                ((q e : ℝ) : ℂ) * (((t e.val.1 + t e.val.2 : ℝ) : ℂ) * Complex.I))) + R) := by
  obtain ⟨C, hC, hscalar⟩ := bernoulli_log_expansion
  refine ⟨C, hC, ?_⟩
  intro q d t hd ht
  let z (e : Edge α) := (((t e.val.1 + t e.val.2 : ℝ) : ℂ) * Complex.I)
  let L (e : Edge α) := Complex.log (1 - ((q e : ℝ) : ℂ) + ((q e : ℝ) : ℂ) * Complex.exp (z e))
  let P (e : Edge α) := bernoulliCumulantPolynomial ((q e : ℝ) : ℂ) (z e)
  let R := ∑ e : Edge α, (L e - P e)
  have hz (e : Edge α) : ‖z e‖ = |t e.val.1 + t e.val.2| :=
    by dsimp only [z]; rw [Complex.norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  refine ⟨R, ?_, ?_⟩
  · unfold R
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e _
    have hs := hscalar (q e : ℝ) (z e) (q e).property (by rw [hz]; exact ht e)
    rwa [hz] at hs
  · have hreal : (∑ i, (d i : ℝ) * t i) =
        ∑ e : Edge α, (q e : ℝ) * (t e.val.1 + t e.val.2) := by
      simp_rw [hd, mul_comm _ (t _)]
      rw [weighted_degree_sum]
      exact Finset.sum_congr rfl (fun e _ ↦ mul_comm _ _)
    have hlin : (∑ i, (d i : ℂ) * (t i : ℂ) * Complex.I) =
        ∑ e : Edge α, ((q e : ℝ) : ℂ) * z e := by
      have hc := congrArg (fun x : ℝ ↦ (x : ℂ) * Complex.I) hreal
      simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast,
        Finset.sum_mul] at hc
      simpa only [z, mul_assoc] using hc
    rw [degreeFourier_eq_exp_log_sum _ _ _ _ (fun e _ ↦ ht e), hlin]
    change Complex.exp (-(∑ e, ((q e : ℝ) : ℂ) * z e) + ∑ e, L e) =
      Complex.exp ((∑ e, (P e - ((q e : ℝ) : ℂ) * z e)) + R)
    congr 1
    unfold R
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    ring

end BoundedEdgeRegularSubgraphs
