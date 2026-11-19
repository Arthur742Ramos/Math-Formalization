module

public import BoundedEdgeRegularSubgraphs.GaussianFrame
public import BoundedEdgeRegularSubgraphs.GaussianEdgeCovariance
import Mathlib.Tactic

/-!
# Covariances of the whitened Gaussian edge forms
-/

public section

open Matrix
open scoped BigOperators MatrixOrder

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]

private theorem gaussian_sqrtInv_transpose (Q : Matrix α α ℝ) :
    ((CFC.sqrt Q)⁻¹)ᵀ = (CFC.sqrt Q)⁻¹ := by
  have h : (CFC.sqrt Q).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg Q)
  have ht : (CFC.sqrt Q)ᵀ = CFC.sqrt Q := by
    ext i j
    simpa only [Matrix.conjTranspose_apply, Matrix.transpose_apply, star_trivial] using
      congrFun (congrFun h.isHermitian.eq i) j
  rw [Matrix.transpose_nonsing_inv, ht]

/-- The form with coefficient vector (B u_e) equals the corresponding
edge sum of (B x). -/
theorem dotProduct_gaussian_whitened_edge (Q : Matrix α α ℝ) (x : α → ℝ) (e : Edge α) :
    let B := (CFC.sqrt Q)⁻¹
    (B *ᵥ realIncidence e) ⬝ᵥ x = (B *ᵥ x) e.val.1 + (B *ᵥ x) e.val.2 := by
  let B := (CFC.sqrt Q)⁻¹
  change (B *ᵥ realIncidence e) ⬝ᵥ x = _
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    gaussian_sqrtInv_transpose]
  exact dotProduct_realIncidence (B *ᵥ x) e

/-- The covariance of two whitened edge forms equals the sum of the four
corresponding entries of the inverse covariance matrix. -/
theorem dotProduct_gaussian_whitened_edges (A : Finset (Edge α))
    (q : Edge α → Set.Icc (0 : ℝ) 1) (hQ : (degreeCovariance A q).PosDef) (e f : Edge α) :
    let Q := degreeCovariance A q
    let B := (CFC.sqrt Q)⁻¹
    (B *ᵥ realIncidence e) ⬝ᵥ (B *ᵥ realIncidence f) = edgePairCovariance Q⁻¹ e f := by
  let Q := degreeCovariance A q
  let B := (CFC.sqrt Q)⁻¹
  have hB : B * Bᵀ = Q⁻¹ := (whitened_degreeCovariance_frame A q hQ).2
  have ht : Bᵀ = B := gaussian_sqrtInv_transpose Q
  have hB' : B * B = Q⁻¹ := by simpa only [ht] using hB
  change (B *ᵥ realIncidence e) ⬝ᵥ (B *ᵥ realIncidence f) = _
  rw [dotProduct_gaussian_whitened_edge Q, Matrix.mulVec_mulVec, hB']
  have hval (i : α) : (Q⁻¹ *ᵥ realIncidence f) i = Q⁻¹ i f.val.1 + Q⁻¹ i f.val.2 := by
    change (Q⁻¹ i) ⬝ᵥ realIncidence f = _
    exact dotProduct_realIncidence _ _
  rw [hval, hval]
  rfl

end BoundedEdgeRegularSubgraphs
