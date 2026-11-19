module

public import BoundedEdgeRegularSubgraphs.GaussianDeterminant
public import BoundedEdgeRegularSubgraphs.GaussianProductParts
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-!
# Integration against the Gaussian quadratic form
-/

public section

open MeasureTheory ProbabilityTheory Set Matrix
open scoped BigOperators ENNReal NNReal MatrixOrder

namespace BoundedEdgeRegularSubgraphs

private theorem standardGaussianProduct_density (n : ℕ) :
    standardGaussianProduct n = (volume : Measure (Fin n → ℝ)).withDensity
      (fun x ↦ ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))) := by
  unfold standardGaussianProduct
  apply Measure.pi_eq
  intro s hs
  let μ := Measure.pi (fun i : Fin n ↦ (volume : Measure ℝ).restrict (s i))
  have hμ : (volume : Measure (Fin n → ℝ)).restrict (Set.pi univ s) = μ :=
    Measure.restrict_pi_pi (fun _ ↦ volume) s
  have hI : Integrable (fun x : Fin n → ℝ ↦ ∏ i, gaussianPDFReal 0 1 (x i)) μ :=
    Integrable.fintype_prod (fun i ↦ (integrable_gaussianPDFReal 0 1).restrict)
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), hμ,
    ← ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ (fun x ↦
      Finset.prod_nonneg (fun i _ ↦ gaussianPDFReal_nonneg 0 1 (x i)))),
    integral_fintype_prod_eq_prod, ENNReal.ofReal_prod_of_nonneg (fun i _ ↦
      integral_nonneg (gaussianPDFReal_nonneg 0 1))]
  exact Finset.prod_congr rfl (fun i _ ↦
    (gaussianReal_apply_eq_integral 0 (one_ne_zero : (1 : ℝ≥0) ≠ 0) (s i)).symm)

private theorem prod_gaussianPDFReal_standard {n : ℕ} (x : Fin n → ℝ) :
    (∏ i, gaussianPDFReal 0 1 (x i)) =
      (Real.sqrt (2 * Real.pi))⁻¹ ^ n * Real.exp (-(∑ i, x i ^ 2) / 2) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_sum,
    ← Finset.sum_div, Finset.sum_neg_distrib]

/-- Gaussian change of variables with the density normalization in (A.3).
The transformed coordinates have covariance `Q⁻¹`. -/
theorem integral_quadratic_smul_eq_gaussianProduct {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosDef) (f : (Fin n → ℝ) → E)
    (hf : StronglyMeasurable f) :
    (∫ x, Real.exp (-(x ⬝ᵥ (Q *ᵥ x)) / 2) • f x) =
      ((Real.sqrt (2 * Real.pi)) ^ n / Real.sqrt Q.det) •
        ∫ y, f ((CFC.sqrt Q)⁻¹ *ᵥ y) ∂standardGaussianProduct n := by
  let R := CFC.sqrt Q
  have hR : R.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg Q)
  have hRQ : R * R = Q := by
    simpa only [pow_two, R] using CFC.sq_sqrt Q hQ.posSemidef.nonneg
  have hRdet : R.det = Real.sqrt Q.det := by
    have h := congrArg Matrix.det hRQ
    rw [Matrix.det_mul, ← pow_two] at h
    rw [← h, Real.sqrt_sq hR.det_nonneg]
  have hRpos : 0 < R.det := by rw [hRdet]; exact Real.sqrt_pos.mpr hQ.det_pos
  have hRun : IsUnit R.det := isUnit_iff_ne_zero.mpr hRpos.ne'
  have hRt : Rᵀ = R := by
    ext i j
    simpa only [Matrix.conjTranspose_apply, Matrix.transpose_apply, star_trivial] using
      congrFun (congrFun hR.isHermitian.eq i) j
  have hquad (x : Fin n → ℝ) : x ⬝ᵥ (Q *ᵥ x) = ∑ i, (R *ᵥ x) i ^ 2 := by
    rw [← hRQ, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hRt]
    simp only [dotProduct, pow_two]
  let G (y : Fin n → ℝ) := Real.exp (-(∑ i, y i ^ 2) / 2) • f (R⁻¹ *ᵥ y)
  have hG : StronglyMeasurable G := by
    apply StronglyMeasurable.smul
    · exact (show Continuous (fun y : Fin n → ℝ ↦ Real.exp (-(∑ i, y i ^ 2) / 2)) by
        fun_prop).stronglyMeasurable
    · exact hf.comp_measurable (Matrix.toLin' R⁻¹).continuous_on_pi.measurable
  have hinv (x : Fin n → ℝ) : R⁻¹ *ᵥ (R *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul R hRun, Matrix.one_mulVec]
  have hx (x : Fin n → ℝ) : Real.exp (-(x ⬝ᵥ (Q *ᵥ x)) / 2) • f x = G (R *ᵥ x) := by
    simp only [G, hquad, hinv]
  have hN : (Real.sqrt (2 * Real.pi)) ^ n ≠ 0 :=
    pow_ne_zero _ (Real.sqrt_pos.mpr (by positivity)).ne'
  have hMeas : Measurable (fun x : Fin n → ℝ ↦ ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))) :=
    ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ (fun i _ ↦
      (measurable_gaussianPDFReal 0 1).comp (measurable_pi_apply i)))
  have hy : (∫ y, f (R⁻¹ *ᵥ y) ∂standardGaussianProduct n) =
      ((Real.sqrt (2 * Real.pi)) ^ n)⁻¹ • ∫ y, G y := by
    rw [standardGaussianProduct_density, integral_withDensity_eq_integral_toReal_smul hMeas
      (ae_of_all _ (fun _ ↦ ENNReal.ofReal_lt_top))]
    simp_rw [ENNReal.toReal_ofReal (Finset.prod_nonneg (fun i _ ↦ gaussianPDFReal_nonneg 0 1 _)),
      prod_gaussianPDFReal_standard, inv_pow, mul_smul, G]
    rw [integral_smul]
  simp_rw [hx]
  change (∫ x, G (Matrix.toLin' R x)) = _
  rw [← integral_map (Matrix.toLin' R).continuous_on_pi.measurable.aemeasurable
      hG.aestronglyMeasurable, Real.map_matrix_volume_pi_eq_smul_volume_pi hRpos.ne',
    integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _),
    abs_of_nonneg (inv_nonneg.mpr hRpos.le), hRdet, hy, smul_smul]
  congr 1
  field_simp [hN]

end BoundedEdgeRegularSubgraphs
