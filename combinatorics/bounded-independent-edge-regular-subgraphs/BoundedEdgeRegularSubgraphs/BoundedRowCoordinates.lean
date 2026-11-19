module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Bounded row coordinates for a matrix of finite rank
-/

public section

open Matrix Set Submodule
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

/-- Select actual rows of the matrix so that every row is a linear
combination of them with all coefficients of absolute value at most one. -/
theorem exists_bounded_matrix_row_coordinates {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ (I : Fin A.rank → Fin n) (c : Fin n → Fin A.rank → ℝ),
      (∀ i a, |c i a| ≤ 1) ∧ ∀ i j, A i j = ∑ a, c i a * A (I a) j := by
  classical
  let V := Submodule.span ℝ (range A.row)
  let u (i : Fin n) : V := ⟨A.row i, Submodule.subset_span (mem_range_self i)⟩
  have hV : Module.finrank ℝ V = A.rank := by
    rw [← Matrix.rank_transpose, Matrix.rank_eq_finrank_span_cols]
    rfl
  have hu : span ℝ (range u) = ⊤ := by
    apply Submodule.map_injective_of_injective V.subtype_injective
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
    rfl
  obtain ⟨κ, b, hb, hsp, hli⟩ := exists_linearIndependent' ℝ u
  letI : Fintype κ := Fintype.ofInjective b hb
  let B₀ : Module.Basis κ ℝ V := Module.Basis.mk hli (by rw [hsp, hu])
  let e : κ ≃ Fin A.rank := Fintype.equivFinOfCardEq ((Module.finrank_eq_card_basis B₀).symm.trans hV)
  let B : Module.Basis (Fin A.rank) ℝ V := B₀.reindex e
  let I₀ : Fin A.rank → Fin n := b ∘ e.symm
  let D (I : Fin A.rank → Fin n) : Matrix (Fin A.rank) (Fin A.rank) ℝ :=
    fun a j ↦ B.repr (u (I a)) j
  have hD₀ : D I₀ = 1 := by
    ext a j
    have he : u (I₀ a) = B a := by
      simp only [B, Module.Basis.reindex_apply, B₀, Module.Basis.mk_apply, I₀, Function.comp_apply]
    change B.repr (u (I₀ a)) j = _
    rw [he, Module.Basis.repr_self_apply, Matrix.one_apply]
  obtain ⟨I, _, hMax⟩ := Finset.exists_max_image Finset.univ
    (fun I ↦ |(D I).det|) ⟨I₀, Finset.mem_univ _⟩
  let M := D I
  have hM : (1 : ℝ) ≤ |M.det| := by
    have h := hMax I₀ (Finset.mem_univ _)
    rw [hD₀, Matrix.det_one, abs_one] at h
    exact h
  have hNe : M.det ≠ 0 := by
    intro h
    rw [h, abs_zero] at hM
    norm_num at hM
  let c (i : Fin n) : Fin A.rank → ℝ := (fun j ↦ B.repr (u i) j) ᵥ* M⁻¹
  have hcoords (i : Fin n) : c i ᵥ* M = fun j ↦ B.repr (u i) j := by
    unfold c
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hNe), Matrix.vecMul_one]
  refine ⟨I, c, ?_, ?_⟩
  · intro i a
    let J := Function.update I a i
    have hd : D J = M.updateRow a (fun j ↦ B.repr (u i) j) := by
      ext p j
      by_cases hp : p = a
      · subst p
        rw [Matrix.updateRow_self]
        simp only [D, J, Function.update_self]
      · rw [Matrix.updateRow_ne hp]
        simp only [D, J, M, Function.update_of_ne hp]
    have hc : (fun j ↦ B.repr (u i) j) = ∑ p, c i p • M p := by
      funext j
      rw [← congrFun (hcoords i) j, Matrix.vecMul_apply]
      simp [Finset.sum_apply, smul_eq_mul, dotProduct]
    have h := hMax J (Finset.mem_univ _)
    rw [hd, hc, Matrix.det_updateRow_sum, smul_eq_mul, abs_mul] at h
    exact (le_of_mul_le_mul_right (by simpa only [one_mul] using h)
      (abs_pos.mpr hNe))
  · intro i j
    have hSum : (∑ a, c i a • u (I a)) = u i := by
      apply B.repr.injective
      ext p
      simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
      have hp := congrFun (hcoords i) p
      rw [Matrix.vecMul_apply] at hp
      exact hp
    have h := congrFun (congrArg (V.subtype : V →ₗ[ℝ] (Fin n → ℝ)) hSum) j
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    exact h.symm

/-- For a symmetric matrix the bounded row coefficients give the same
factorization on both sides of the selected principal submatrix. -/
theorem exists_bounded_matrix_symmetric_coordinates {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) :
    ∃ (I : Fin A.rank → Fin n) (c : Fin n → Fin A.rank → ℝ),
      (∀ i a, |c i a| ≤ 1) ∧
        ∀ i j, A i j = ∑ a, ∑ b, c i a * A (I a) (I b) * c j b := by
  obtain ⟨I, c, hc, h⟩ := exists_bounded_matrix_row_coordinates A
  refine ⟨I, c, hc, fun i j ↦ ?_⟩
  have hSym (i j : Fin n) : A i j = A j i :=
    (congrFun (congrFun hA.eq j) i : A i j = A j i)
  rw [h i j]
  apply Finset.sum_congr rfl
  intro a _
  rw [hSym (I a) j, h j (I a), Finset.mul_sum]
  exact Finset.sum_congr rfl (fun b _ ↦ by rw [hSym (I b) (I a)]; ring)

end BoundedEdgeRegularSubgraphs
