module

public import BoundedEdgeRegularSubgraphs.DeterminantRatio
public import BoundedEdgeRegularSubgraphs.GaussianParts
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
# The normalization of the Gaussian quadratic form
-/

public section

open MeasureTheory
open scoped BigOperators Matrix MatrixOrder

namespace BoundedEdgeRegularSubgraphs

/-- The Gaussian integral associated with a positive definite quadratic form. -/
theorem integral_exp_neg_quadratic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosDef) :
    (∫ x : ι → ℝ, Real.exp (-(x ⬝ᵥ (A *ᵥ x)) / 2)) =
      (Real.sqrt (2 * Real.pi)) ^ Fintype.card ι / Real.sqrt A.det := by
  let R := CFC.sqrt A
  have hR : R.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  have hRA : R * R = A := by
    simpa only [pow_two, R] using CFC.sq_sqrt A hA.posSemidef.nonneg
  have hRdet : R.det ^ 2 = A.det := by
    simpa only [Matrix.det_mul, pow_two] using congrArg Matrix.det hRA
  have hRdet' : R.det = Real.sqrt A.det := by
    rw [← hRdet, Real.sqrt_sq hR.det_nonneg]
  have hRpos : 0 < R.det := by rw [hRdet']; exact Real.sqrt_pos.mpr hA.det_pos
  have hRtranspose : Rᵀ = R := by
    ext i j
    have h := congrFun (congrFun hR.isHermitian.eq i) j
    simpa only [Matrix.conjTranspose_apply, Matrix.transpose_apply, star_trivial] using h
  have hquad (x : ι → ℝ) : x ⬝ᵥ (A *ᵥ x) = ∑ i, (R *ᵥ x) i ^ 2 := by
    rw [← hRA, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
      hRtranspose]
    simp only [dotProduct, pow_two]
  let G (x : ι → ℝ) := ∏ i, standardNormalKernel (x i)
  have hG (x : ι → ℝ) : Real.exp (-(x ⬝ᵥ (A *ᵥ x)) / 2) = G (Matrix.toLin' R x) := by
    rw [hquad]
    change Real.exp (-(∑ i, (R *ᵥ x) i ^ 2) / 2) = ∏ i, Real.exp (-((R *ᵥ x) i ^ 2 / 2))
    simp only [← Real.exp_sum, ← neg_div, ← Finset.sum_div, Finset.sum_neg_distrib]
  have hGmeas : Measurable G := by
    dsimp only [G, standardNormalKernel]
    exact Finset.measurable_prod _ (fun i _ ↦ by fun_prop)
  have hdiag :
      (∫ x : ι → ℝ, G x) = (Real.sqrt (2 * Real.pi)) ^ Fintype.card ι := by
    dsimp only [G]
    rw [integral_fintype_prod_volume_eq_pow]
    congr 1
    have hi : (∫ x : ℝ, standardNormalKernel x) = Real.sqrt (Real.pi / (1 / 2)) := by
      have hpt (x : ℝ) : standardNormalKernel x = Real.exp (-(1 / 2 : ℝ) * x ^ 2) := by
        dsimp only [standardNormalKernel]
        congr 1
        ring
      simp_rw [hpt]
      exact integral_gaussian (1 / 2)
    rw [hi]
    congr 1
    field_simp
  simp_rw [hG]
  rw [← integral_map (Matrix.toLin' R).continuous_on_pi.measurable.aemeasurable
      hGmeas.aestronglyMeasurable, Real.map_matrix_volume_pi_eq_smul_volume_pi hRpos.ne',
    integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _),
    abs_of_nonneg (inv_nonneg.mpr hRpos.le), smul_eq_mul, hdiag, hRdet']
  ring

end BoundedEdgeRegularSubgraphs
