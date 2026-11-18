module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# A determinant ratio for adding a positive semidefinite matrix
-/

public section

open scoped BigOperators Matrix MatrixOrder
open Matrix

namespace BoundedEdgeRegularSubgraphs

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option maxHeartbeats 1000000 in
/-- The determinant of one plus a positive semidefinite matrix is bounded by
the exponential of its trace. -/
theorem det_one_add_le_exp_trace (B : Matrix ι ι ℝ) (hB : B.PosSemidef) :
    (1 + B).det ≤ Real.exp B.trace := by
  let u := hB.isHermitian.eigenvectorUnitary
  let F := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) u
  let eig := hB.isHermitian.eigenvalues
  have hn (i : ι) : 0 ≤ eig i := hB.eigenvalues_nonneg i
  have hs : B = F (Matrix.diagonal eig) := by
    simpa [F, eig, u] using hB.isHermitian.spectral_theorem
  have hprod : (star u : Matrix ι ι ℝ).det * (u : Matrix ι ι ℝ).det = 1 := by
    simpa only [Matrix.det_mul, Matrix.det_one] using
      congrArg Matrix.det (Unitary.coe_star_mul_self u)
  have hdet (X : Matrix ι ι ℝ) : (F X).det = X.det := by
    dsimp only [F]
    rw [Unitary.conjStarAlgAut_apply, Matrix.det_mul, Matrix.det_mul]
    calc
      _ = ((star u : Matrix ι ι ℝ).det * (u : Matrix ι ι ℝ).det) * X.det := by ring
      _ = _ := by rw [hprod, one_mul]
  have hsum : B.trace = ∑ i, eig i := by
    simpa [eig] using hB.isHermitian.trace_eq_sum_eigenvalues
  have hd : 1 + B = F (Matrix.diagonal fun i ↦ 1 + eig i) := by
    rw [hs]
    have hadd : Matrix.diagonal (fun i ↦ 1 + eig i) =
        (1 : Matrix ι ι ℝ) + Matrix.diagonal eig := by
      ext i j
      by_cases h : i = j <;> simp [h]
    rw [hadd, map_add, map_one]
  rw [hd, hdet, Matrix.det_diagonal, hsum]
  exact Real.prod_one_add_le_exp_sum Finset.univ hn

/-- Adding a positive semidefinite matrix costs at most the exponential of the
trace of the relative perturbation. -/
theorem det_add_le_det_mul_exp_trace (A P : Matrix ι ι ℝ)
    (hA : A.PosDef) (hP : P.PosSemidef) :
    (A + P).det ≤ A.det * Real.exp (A⁻¹ * P).trace := by
  let R := CFC.sqrt A
  let L := R⁻¹
  let B := L * P * L
  have hR : R.PosSemidef := (CFC.sqrt_nonneg A).posSemidef
  have hL : L.PosSemidef := hR.inv
  have hRA : R * R = A := by
    simpa only [pow_two, R] using CFC.sq_sqrt A hA.posSemidef.nonneg
  have hdetRA : R.det * R.det = A.det := by
    simpa only [Matrix.det_mul] using congrArg Matrix.det hRA
  have hdetA : IsUnit A.det := isUnit_iff_ne_zero.mpr hA.det_pos.ne'
  have hdetR : IsUnit R.det := isUnit_iff_ne_zero.mpr (fun h =>
    hA.det_pos.ne' (by simpa [h] using hdetRA.symm))
  have hRL : R * L = 1 := Matrix.mul_nonsing_inv R hdetR
  have hLR : L * R = 1 := Matrix.nonsing_inv_mul R hdetR
  have hLL : L * L = A⁻¹ := by
    have h : A * (L * L) = 1 := by
      rw [← hRA]
      calc
        _ = R * (R * L) * L := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hRL, mul_one, hRL]
    calc
      _ = (A⁻¹ * A) * (L * L) := by rw [Matrix.nonsing_inv_mul A hdetA, one_mul]
      _ = _ := by rw [Matrix.mul_assoc, h, mul_one]
  have hB : B.PosSemidef := by
    have he : Lᴴ = L := hL.isHermitian
    simpa only [B, he] using hP.conjTranspose_mul_mul_same L
  have htrace : B.trace = (A⁻¹ * P).trace := by
    dsimp only [B]
    rw [Matrix.trace_mul_cycle, hLL]
  have hfactor : A + P = R * (1 + B) * R := by
    dsimp only [B]
    symm
    calc
      _ = R * R + (R * L) * P * (L * R) := by noncomm_ring
      _ = _ := by rw [hRA, hRL, hLR, one_mul, mul_one]
  rw [hfactor, Matrix.det_mul, Matrix.det_mul]
  calc
    _ = A.det * (1 + B).det := by rw [← hdetRA]; ring
    _ ≤ _ := by
      rw [← htrace]
      exact mul_le_mul_of_nonneg_left (det_one_add_le_exp_trace B hB) hA.det_pos.le

end BoundedEdgeRegularSubgraphs
