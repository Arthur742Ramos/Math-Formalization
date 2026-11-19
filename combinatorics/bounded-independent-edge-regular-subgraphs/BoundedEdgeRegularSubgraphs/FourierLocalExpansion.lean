module

public import BoundedEdgeRegularSubgraphs.CenteredFourierExpansion
public import BoundedEdgeRegularSubgraphs.GaussianQuarticClipping
public import BoundedEdgeRegularSubgraphs.Covariance
import Mathlib.Analysis.Complex.Arg
import Mathlib.Tactic

/-!
# The local Fourier expansion on any available edge set
-/

@[expose] public section

open MeasureTheory Matrix
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- Cubic coefficient in the degree Fourier expansion. -/
noncomputable def degreeCubicCoefficient (q : ℝ) : ℝ := q * (1 - q) * (2 * q - 1) / 6

/-- Quartic coefficient in the degree Fourier expansion. -/
noncomputable def degreeQuarticCoefficient (q : ℝ) : ℝ := q * (1 - q) * (1 - 6 * (q * (1 - q))) / 24

/-- The cubic term in real angle coordinates. -/
noncomputable def edgeCubic (A : Finset (Edge α)) (a : Edge α → ℝ) (x : α → ℝ) : ℝ :=
  ∑ e ∈ A, a e * (x e.val.1 + x e.val.2) ^ 3

theorem abs_degreeCubicCoefficient_le (q : Set.Icc (0 : ℝ) 1) :
    |degreeCubicCoefficient q| ≤ 1 / 24 := by
  have hq₀ := q.property.1
  have hq₁ := q.property.2
  have hw : 0 ≤ (q : ℝ) * (1 - q) := mul_nonneg hq₀ (sub_nonneg.mpr hq₁)
  have hw' : (q : ℝ) * (1 - q) ≤ 1 / 4 := by nlinarith only [sq_nonneg ((q : ℝ) - 1 / 2)]
  have h : |2 * (q : ℝ) - 1| ≤ 1 :=
    abs_le.mpr ⟨by linarith only [hq₀], by linarith only [hq₁]⟩
  unfold degreeCubicCoefficient
  rw [abs_div, abs_mul, abs_of_nonneg hw, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
  have hh := mul_le_mul hw' h (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 4)
  linarith only [hh]

theorem abs_degreeQuarticCoefficient_le (q : Set.Icc (0 : ℝ) 1) :
    |degreeQuarticCoefficient q| ≤ 1 / 96 := by
  have hw : 0 ≤ (q : ℝ) * (1 - q) := mul_nonneg q.property.1 (sub_nonneg.mpr q.property.2)
  have hw' : (q : ℝ) * (1 - q) ≤ 1 / 4 := by nlinarith only [sq_nonneg ((q : ℝ) - 1 / 2)]
  have h : |1 - 6 * ((q : ℝ) * (1 - q))| ≤ 1 :=
    abs_le.mpr ⟨by linarith only [hw'], by linarith only [hw]⟩
  unfold degreeQuarticCoefficient
  rw [abs_div, abs_mul, abs_of_nonneg hw, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 24)]
  have hh := mul_le_mul hw' h (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 4)
  linarith only [hh]

/-- A fixed choice of the Taylor remainder, also for the deleted array. -/
noncomputable def degreeFourierLocalError (A : Finset (Edge α))
    (q : Edge α → Set.Icc (0 : ℝ) 1) (t : α → ℝ) : ℂ :=
  ∑ e ∈ A, let z := ((t e.val.1 + t e.val.2 : ℝ) : ℂ) * Complex.I
    Complex.log (1 - ((q e : ℝ) : ℂ) + ((q e : ℝ) : ℂ) * Complex.exp z) -
      bernoulliCumulantPolynomial ((q e : ℝ) : ℂ) z

theorem measurable_degreeFourierLocalError (A : Finset (Edge α))
    (q : Edge α → Set.Icc (0 : ℝ) 1) : Measurable (degreeFourierLocalError A q) := by
  unfold degreeFourierLocalError
  apply Finset.measurable_sum
  intro e _
  unfold bernoulliCumulantPolynomial
  fun_prop

/-- The same fifth-order bound works for every available edge set. -/
theorem norm_degreeFourierLocalError_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : Finset (Edge α)) (q : Edge α → Set.Icc (0 : ℝ) 1) (t : α → ℝ),
      (∀ e ∈ A, |t e.val.1 + t e.val.2| ≤ 1 / 4) →
      ‖degreeFourierLocalError A q t‖ ≤ C * ∑ e ∈ A, |t e.val.1 + t e.val.2| ^ 5 := by
  obtain ⟨C, hC, h⟩ := bernoulli_log_expansion
  refine ⟨C, hC, fun A q t ht ↦ ?_⟩
  unfold degreeFourierLocalError
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e he
  let z := ((t e.val.1 + t e.val.2 : ℝ) : ℂ) * Complex.I
  have hz : ‖z‖ = |t e.val.1 + t e.val.2| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hh := h (q e : ℝ) z (q e).property (hz.trans_le (ht e he))
  rwa [hz] at hh

/-- The Fourier integrand with the quadratic, cubic, quartic and linear
terms written in real coordinates. The linear term drops from the modulus. -/
theorem degreeFourier_eq_exp_local_expansion (A : Finset (Edge α))
    (q : Edge α → Set.Icc (0 : ℝ) 1) (d : α → ℤ) (t : α → ℝ)
    (ht : ∀ e ∈ A, |t e.val.1 + t e.val.2| ≤ 1 / 4) :
    let f := edgeCubic A (fun e ↦ degreeCubicCoefficient (q e)) t
    let h := edgeQuartic A (fun e ↦ degreeQuarticCoefficient (q e)) t
    let l := (∑ e ∈ A, (q e : ℝ) * (t e.val.1 + t e.val.2)) - ∑ i, (d i : ℝ) * t i
    degreeFourier A q d (fun i ↦ (t i : PhaseCircle)) =
      Complex.exp (((-(t ⬝ᵥ (degreeCovariance A q *ᵥ t)) / 2 + h : ℝ) : ℂ) +
        ((f + l : ℝ) : ℂ) * Complex.I + degreeFourierLocalError A q t) := by
  let s (e : Edge α) := t e.val.1 + t e.val.2
  let w (e : Edge α) := (q e : ℝ) * (1 - q e)
  let z (e : Edge α) := (s e : ℂ) * Complex.I
  let P (e : Edge α) := bernoulliCumulantPolynomial (q e : ℝ) (z e)
  let L (e : Edge α) := Complex.log (1 - ((q e : ℝ) : ℂ) + ((q e : ℝ) : ℂ) * Complex.exp (z e))
  let F := ∑ e ∈ A, degreeCubicCoefficient (q e) * s e ^ 3
  let H := ∑ e ∈ A, degreeQuarticCoefficient (q e) * s e ^ 4
  let qform := t ⬝ᵥ (degreeCovariance A q *ᵥ t)
  let l := (∑ e ∈ A, (q e : ℝ) * s e) - ∑ i, (d i : ℝ) * t i
  change degreeFourier A q d (fun i ↦ (t i : PhaseCircle)) =
    Complex.exp (((-qform / 2 + H : ℝ) : ℂ) + ((F + l : ℝ) : ℂ) * Complex.I +
      ∑ e ∈ A, (L e - P e))
  have hquad : qform = ∑ e ∈ A, w e * s e ^ 2 := by
    rw [← degreeCovariance_quadratic]
    simp only [qform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have hp (e : Edge α) : P e =
      (((-w e * s e ^ 2 / 2 + degreeQuarticCoefficient (q e) * s e ^ 4 : ℝ) : ℂ)) +
        ((degreeCubicCoefficient (q e) * s e ^ 3 + (q e : ℝ) * s e : ℝ) : ℂ) * Complex.I := by
    have h := bernoulliCumulantPolynomial_imaginary (q e : ℝ) (s e)
    change P e - (q e : ℝ) * z e = _ at h
    dsimp only [z, w, degreeQuarticCoefficient, degreeCubicCoefficient] at *
    push_cast at *
    linear_combination h
  rw [degreeFourier_eq_exp_log_sum A q d t ht]
  congr 1
  change -(∑ i, (d i : ℂ) * (t i : ℂ) * Complex.I) + ∑ e ∈ A, L e = _
  rw [Finset.sum_sub_distrib]
  have hP : (∑ e ∈ A, P e) = ((-qform / 2 + H : ℝ) : ℂ) +
      ((F + ∑ e ∈ A, (q e : ℝ) * s e : ℝ) : ℂ) * Complex.I := by
    simp_rw [hp]
    rw [hquad]
    dsimp only [F, H]
    push_cast
    simp only [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_neg_distrib,
      ← Finset.sum_mul, neg_mul]
  rw [hP]
  dsimp only [l]
  push_cast
  rw [← Finset.sum_mul]
  ring

/-- Local modulus formula for every target, including residual degree vectors. -/
theorem norm_degreeFourier_eq_exp_local_expansion (A : Finset (Edge α))
    (q : Edge α → Set.Icc (0 : ℝ) 1) (d : α → ℤ) (t : α → ℝ)
    (ht : ∀ e ∈ A, |t e.val.1 + t e.val.2| ≤ 1 / 4) :
    ‖degreeFourier A q d (fun i ↦ (t i : PhaseCircle))‖ =
      Real.exp (-(t ⬝ᵥ (degreeCovariance A q *ᵥ t)) / 2 +
        edgeQuartic A (fun e ↦ degreeQuarticCoefficient (q e)) t +
        (degreeFourierLocalError A q t).re) := by
  rw [degreeFourier_eq_exp_local_expansion A q d t ht, Complex.norm_exp]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]

end BoundedEdgeRegularSubgraphs
