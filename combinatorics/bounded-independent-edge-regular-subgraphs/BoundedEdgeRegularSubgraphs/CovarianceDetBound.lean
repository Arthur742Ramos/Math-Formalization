module

public import BoundedEdgeRegularSubgraphs.OverlapDeterminant
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic

/-!
# Bounding the determinant by the upper spectral bound
-/

public section

open scoped BigOperators Matrix

namespace BoundedEdgeRegularSubgraphs

/-- An upper quadratic-form bound controls the determinant of a positive
semidefinite matrix. -/
theorem det_le_pow_of_quadratic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosSemidef) {M : ℝ}
    (hquad : ∀ v : ι → ℝ, v ⬝ᵥ (A *ᵥ v) ≤ M * ∑ i, v i ^ 2) :
    A.det ≤ M ^ Fintype.card ι := by
  let hH := hA.isHermitian
  rw [hH.det_eq_prod_eigenvalues]
  change (∏ i : ι, hH.eigenvalues i) ≤ M ^ Fintype.card ι
  rw [← Finset.card_univ, ← Finset.prod_const]
  apply Finset.prod_le_prod₀ (fun i _ ↦ hA.eigenvalues_nonneg i)
  intro i _
  let v : EuclideanSpace ℝ ι := hH.eigenvectorBasis i
  have hn : (∑ j, v j ^ 2) = 1 := by
    have h := EuclideanSpace.norm_sq_eq v
    simp only [Real.norm_eq_abs, sq_abs] at h
    rw [← h, hH.eigenvectorBasis.orthonormal.1 i, one_pow]
  have h := hH.eigenvalues_eq i
  have he : hH.eigenvalues i = (⇑v : ι → ℝ) ⬝ᵥ (A *ᵥ ⇑v) := by
    simpa only [RCLike.re_to_real, star_trivial, v] using h
  rw [he]
  simpa only [hn, mul_one] using hquad ⇑v

/-- The determinant upper bound appearing in the degree-atom normalization. -/
theorem degreeCovariance_outside_overlap_det_le {α : Type*} [Fintype α] [LinearOrder α]
    (S : Finset α) (hm : 3 ≤ ((Finset.univ : Finset α) \ S).card)
    (p : Edge α → Set.Icc (0 : ℝ) 1) :
    (degreeCovariance (edgesOutsideOverlap S) p).det ≤
      (((Fintype.card α : ℝ) - 1) / 2) ^ Fintype.card α := by
  classical
  let A := edgesOutsideOverlap S
  have hsymm : (degreeCovariance A p).IsHermitian := by
    ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, degreeCovariance]
    exact Finset.sum_congr rfl (fun e _ ↦ by ring)
  have hPSD : (degreeCovariance A p).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hsymm
    intro x
    rw [star_trivial, Matrix.dot_mulVec_eq_sum_sum, Finset.sum_comm]
    exact degreeCovariance_quadratic_nonneg A p x
  apply det_le_pow_of_quadratic _ hPSD
  intro v
  rw [Matrix.dot_mulVec_eq_sum_sum, Finset.sum_comm]
  have hzero (e : Edge α) : 0 ≤ (p e : ℝ) * (1 - p e) :=
    mul_nonneg (p e).property.1 (sub_nonneg.mpr (p e).property.2)
  exact (degreeCovariance_outside_overlap_bounds S hm p 0 le_rfl hzero v).2

end BoundedEdgeRegularSubgraphs
