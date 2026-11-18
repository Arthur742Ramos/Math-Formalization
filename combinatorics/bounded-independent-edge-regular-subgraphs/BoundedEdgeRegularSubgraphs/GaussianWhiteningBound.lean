module

public import BoundedEdgeRegularSubgraphs.GaussianChangeOfVariables
import Mathlib.Tactic

/-!
# Norm and coordinate variance bounds for the Gaussian linear map
-/

public section

open Matrix
open scoped BigOperators MatrixOrder

namespace BoundedEdgeRegularSubgraphs

/-- A lower quadratic bound for the covariance inverse bounds the
norm of the Gaussian linear map and its coordinate variances. -/
theorem gaussian_inverse_sqrt_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℝ) (hQ : Q.PosDef) {lower : ℝ} (hlower : 0 < lower)
    (hquad : ∀ x : ι → ℝ, lower * ∑ i, x i ^ 2 ≤ x ⬝ᵥ (Q *ᵥ x)) :
    let B := (CFC.sqrt Q)⁻¹
    (∀ x : ι → ℝ, (∑ i, (B *ᵥ x) i ^ 2) ≤ lower⁻¹ * ∑ i, x i ^ 2) ∧
      (∀ i, (∑ j, (B i j) ^ 2) ≤ lower⁻¹) := by
  let R := CFC.sqrt Q
  let B := R⁻¹
  have hR : R.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg Q)
  have hRQ : R * R = Q := by
    simpa only [pow_two, R] using CFC.sq_sqrt Q hQ.posSemidef.nonneg
  have hRd : R.det ≠ 0 := by
    intro h
    have hh := congrArg Matrix.det hRQ
    rw [Matrix.det_mul, h, zero_mul] at hh
    exact hQ.det_pos.ne' hh.symm
  have hRt : Rᵀ = R := by
    ext i j
    simpa only [Matrix.conjTranspose_apply, Matrix.transpose_apply, star_trivial] using
      congrFun (congrFun hR.isHermitian.eq i) j
  have hBt : Bᵀ = B := by
    dsimp only [B]
    rw [Matrix.transpose_nonsing_inv, hRt]
  have hRB : R * B = 1 := Matrix.mul_nonsing_inv R (isUnit_iff_ne_zero.mpr hRd)
  have hq (x : ι → ℝ) : x ⬝ᵥ (Q *ᵥ x) = ∑ i, (R *ᵥ x) i ^ 2 := by
    rw [← hRQ, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hRt]
    simp only [dotProduct, pow_two]
  have hn (x : ι → ℝ) : (∑ i, (B *ᵥ x) i ^ 2) ≤ lower⁻¹ * ∑ i, x i ^ 2 := by
    have hh := hquad (B *ᵥ x)
    rw [hq, Matrix.mulVec_mulVec, hRB, Matrix.one_mulVec] at hh
    rw [mul_comm, ← div_eq_mul_inv]
    exact (le_div_iff₀ hlower).2 (by simpa only [mul_comm] using hh)
  refine ⟨hn, fun i ↦ ?_⟩
  let v : ι → ℝ := Pi.single i 1
  have h := hn v
  have hs : (∑ j, v j ^ 2) = 1 := by simp [v, Pi.single_apply]
  rw [hs, mul_one] at h
  dsimp only [v] at h
  rw [Matrix.mulVec_single_one] at h
  have hh (j : ι) : B j i = B i j := congrFun (congrFun hBt i) j
  simpa only [Matrix.col_apply, hh] using h

end BoundedEdgeRegularSubgraphs
