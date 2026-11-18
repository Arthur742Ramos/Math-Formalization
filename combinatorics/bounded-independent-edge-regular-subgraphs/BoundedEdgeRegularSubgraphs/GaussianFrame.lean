module

public import BoundedEdgeRegularSubgraphs.GaussianDeterminant
public import BoundedEdgeRegularSubgraphs.GaussianEdgeCovariance
public import BoundedEdgeRegularSubgraphs.Covariance
import Mathlib.Tactic

/-!
# Normalization of the whitened edge incidence vectors
-/

public section

open Matrix
open scoped BigOperators MatrixOrder

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- The real incidence vector of one edge. -/
def realIncidence (e : Edge α) (i : α) : ℝ := edgeIncidence e i

private theorem dotProduct_realIncidence (x : α → ℝ) (e : Edge α) :
    x ⬝ᵥ realIncidence e = x e.val.1 + x e.val.2 := by
  classical
  simp only [dotProduct, realIncidence, edgeIncidence, Int.cast_add, Int.cast_ite, Int.cast_one,
    Int.cast_zero, mul_add, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-- The square-root change of variables makes the edge vectors a weighted
frame with identity frame operator, as used in (A.2). -/
theorem whitened_degreeCovariance_frame (A : Finset (Edge α))
    (p : Edge α → Set.Icc (0 : ℝ) 1) (hpos : (degreeCovariance A p).PosDef) :
    let Q := degreeCovariance A p
    let B := (CFC.sqrt Q)⁻¹
    let v (e : Edge α) := B *ᵥ realIncidence e
    (∀ x : α → ℝ, (∑ e ∈ A, ((p e : ℝ) * (1 - p e)) * (x ⬝ᵥ v e) ^ 2) =
      ∑ i, x i ^ 2) ∧ B * Bᵀ = Q⁻¹ := by
  classical
  intro Q B v
  let R := CFC.sqrt Q
  have hR : R.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg Q)
  have hRQ : R * R = Q := by
    simpa only [pow_two, R] using CFC.sq_sqrt Q hpos.posSemidef.nonneg
  have hRdet : R.det ≠ 0 := by
    intro h
    have ht := congrArg Matrix.det hRQ
    rw [Matrix.det_mul, h, zero_mul] at ht
    exact hpos.det_pos.ne' ht.symm
  have hRT : Rᵀ = R := by
    ext i j
    have h := congrFun (congrFun hR.isHermitian.eq i) j
    simpa only [Matrix.conjTranspose_apply, Matrix.transpose_apply, star_trivial] using h
  have hBT : B.transpose = B := by
    change (R⁻¹).transpose = R⁻¹
    rw [Matrix.transpose_nonsing_inv, hRT]
  have hBu : B * R = 1 := Matrix.nonsing_inv_mul R (isUnit_iff_ne_zero.mpr hRdet)
  have hRu : R * B = 1 := Matrix.mul_nonsing_inv R (isUnit_iff_ne_zero.mpr hRdet)
  have hId : B * Q * Bᵀ = 1 := by
    rw [hBT, ← hRQ, ← mul_assoc, hBu, one_mul, hRu]
  constructor
  · intro x
    let y := Bᵀ *ᵥ x
    have hdot (e : Edge α) : x ⬝ᵥ v e = y e.val.1 + y e.val.2 := by
      change x ⬝ᵥ (B *ᵥ realIncidence e) = _
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
      exact dotProduct_realIncidence y e
    simp_rw [hdot]
    rw [← degreeCovariance_quadratic]
    change (∑ i, ∑ j, y i * Q i j * y j) = _
    have hquad : (∑ i, ∑ j, y i * Q i j * y j) = y ⬝ᵥ (Q *ᵥ y) := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    have hmove : x ⬝ᵥ (B *ᵥ (Q *ᵥ y)) = y ⬝ᵥ (Q *ᵥ y) := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    rw [hquad, ← hmove]
    dsimp only [y]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hId, Matrix.one_mulVec]
    simp only [dotProduct, pow_two]
  · rw [hBT]
    change R⁻¹ * R⁻¹ = Q⁻¹
    rw [← hRQ, Matrix.mul_inv_rev]

end BoundedEdgeRegularSubgraphs
