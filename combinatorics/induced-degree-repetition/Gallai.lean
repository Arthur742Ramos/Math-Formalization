module

public import Statement
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.CharP.Two

public section
namespace InducedDegreeRepetition

open Finset Matrix

variable {V : Type*} [Fintype V]

private theorem bitCases (x : ZMod 2) : x = 0 ∨ x = 1 := (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) x

/-- Off-diagonal terms of a symmetric form occur in pairs in characteristic two. -/
private theorem offDiagSum (A : Matrix V V (ZMod 2)) (hs : ∀ i j, A i j = A j i)
    (hz : ∀ i, A i i = 0) (z : V → ZMod 2) :
    (∑ i, ∑ j, z i * (A i j * z j)) = 0 := by
  rw [← Fintype.sum_prod_type (fun v : V × V => z v.1 * (A v.1 v.2 * z v.2))]
  apply Finset.sum_ninvolution Prod.swap
  · intro ⟨i,j⟩
    change z i * (A i j * z j) + z j * (A j i * z i) = 0
    rw [hs j i, show z j * (A i j * z i) = z i * (A i j * z j) by ac_rfl]
    exact CharTwo.add_self_eq_zero _
  · rintro ⟨i,j⟩ hn he
    have hij : j = i := congrArg Prod.fst he
    subst j
    simp [hz] at hn
  · simp
  · simp

/-- Solve the parity system using separation of a vector from a subspace. -/
private theorem solveParity (A : Matrix V V (ZMod 2)) (hs : ∀ i j, A i j = A j i)
    (hz : ∀ i, A i i = 0) (d : V → ZMod 2) :
    ∃ s : V → ZMod 2, ∀ i, (∑ j, A i j * s j) + d i * s i = d i := by
  classical
  let M := A + diagonal d
  have h : d ∈ LinearMap.range M.mulVecLin := by
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff (LinearMap.range M.mulVecLin) d).mp
    intro φ hφ
    let z := fun i : V => φ (Pi.single i 1)
    have evalφ (v : V → ZMod 2) : φ v = ∑ i, v i * z i := by
      have he : (∑ i, v i • Pi.single i (1 : ZMod 2)) = v := by
        ext j
        simp [Pi.single_apply, Finset.sum_apply]
      rw [← he, map_sum]
      simp only [map_smul, smul_eq_mul]
      rw [he]
    have hcol (i : V) : (∑ j, A i j * z j) + d i * z i = 0 := by
      have hm := (Submodule.mem_dualAnnihilator _ |>.mp hφ) (M.mulVecLin (Pi.single i 1))
        (LinearMap.mem_range_self _ _)
      rw [evalφ] at hm
      simpa [M, Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col,
        add_mul, Finset.sum_add_distrib, Matrix.diagonal_apply, ite_mul, hs _ i] using hm
    have hsum := Finset.sum_congr (s₁ := Finset.univ) (g := fun _ => (0 : ZMod 2)) rfl
      (fun i _ => show z i * ((∑ j, A i j * z j) + d i * z i) = 0 by rw [hcol, mul_zero])
    simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib, offDiagSum A hs hz,
      zero_add, Finset.sum_const_zero] at hsum
    rw [evalφ]
    convert hsum using 1
    apply Finset.sum_congr rfl
    intro i _
    rcases bitCases (z i) with h | h <;> simp [h]
  obtain ⟨s, hs'⟩ := h
  refine ⟨s, fun i => ?_⟩
  simpa [M, Matrix.mulVecLin_apply, Matrix.add_mulVec, Matrix.mulVec_diagonal,
    Matrix.diagonal_apply, ite_mul, Matrix.mulVec, dotProduct] using congrFun hs' i

/-- Gallai's partition into two induced subgraphs of even degrees, as used in §6. -/
theorem gallai_even_partition [DecidableEq V] (G : SimpleGraph V) :
    ∃ S : Finset V, (∀ x ∈ S, Even (degreeOn G S x)) ∧
      (∀ x ∈ Sᶜ, Even (degreeOn G Sᶜ x)) := by
  classical
  let A : Matrix V V (ZMod 2) := fun i j => if G.Adj i j then 1 else 0
  let d := fun i => ∑ j, A i j
  obtain ⟨s, hs⟩ := solveParity A (fun i j => by simp only [A, G.adj_comm i j])
    (fun i => by simp [A]) d
  let S := univ.filter fun i => s i = 1
  refine ⟨S, ?_, ?_⟩
  · intro i hi
    have hi' := (mem_filter.mp hi).2
    have hz : (∑ j, A i j * s j) = 0 := by simpa [hi'] using hs i
    apply ZMod.natCast_eq_zero_iff_even.mp
    rw [← hz, degreeOn, ← Finset.sum_boole]
    simp only [S, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    rcases bitCases (s j) with h | h <;> simp [A, h]
  · intro i hi
    have hi' : s i = 0 := (bitCases _).resolve_right (by simpa [S] using hi)
    have hz : (∑ j, A i j * s j) = d i := by simpa [hi'] using hs i
    apply ZMod.natCast_eq_zero_iff_even.mp
    calc
      _ = ∑ j, (A i j - A i j * s j) := by
        rw [degreeOn, ← Finset.sum_boole]
        simp only [S, Finset.compl_filter]
        simp only [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro j _
        rcases bitCases (s j) with h | h <;> simp [A, h]
      _ = 0 := by rw [Finset.sum_sub_distrib, hz, ← show (∑ j, A i j) = d i from rfl, sub_self]

end InducedDegreeRepetition
