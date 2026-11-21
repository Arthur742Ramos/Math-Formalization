module

public import SampledModel
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Positivity

public section
namespace InducedDegreeRepetition.Restriction

open Finset Submodule Matrix
open scoped Classical
variable {q : ℕ} [NeZero q] {I J : Type*} [Fintype I] [Fintype J]

omit [Fintype I] in
/-- A translate of a subgroup generates at most q times as many elements. -/
theorem coset_row_span (M : Matrix I J (ZMod q)) (H : AddSubgroup (J → ZMod q)) (z : J → ZMod q)
    (mem : ∀ i, M.row i - z ∈ H) :
    Nat.card (span (ZMod q) (Set.range M.row)) ≤ q*Nat.card H := by
  classical
  let p : (ZMod q × H) →ₗ[ZMod q] (J → ZMod q) :=
    { toFun := fun v => v.1 • z + v.2.val
      map_add' := by intro v w; change (v.1+w.1) • z + (v.2.val+w.2.val) = _; rw [add_smul]; abel
      map_smul' := by intro a v; change (a*v.1) • z + a • v.2.val = a • (v.1 • z + v.2.val); rw [smul_add,mul_smul] }
  have le : span (ZMod q) (Set.range M.row) ≤ LinearMap.range p := by
    apply span_le.mpr
    rintro _ ⟨i,rfl⟩
    refine ⟨(1,⟨M.row i-z,mem i⟩),?_⟩
    change (1:ZMod q) • z + (M.row i-z) = _
    rw [one_smul]; abel
  have sur : Function.Surjective p.rangeRestrict := by rintro ⟨_,a,rfl⟩; exact ⟨a,rfl⟩
  have size := (Nat.card_le_card_of_injective _ (Submodule.inclusion_injective le)).trans
    (Nat.card_le_card_of_surjective _ sur)
  simpa [Nat.card_prod] using size

/-- A sampled matrix of small image has generating row and column positions,
both with the logarithmic size bound and both chosen from the actual sample. -/
theorem generating_positions (M : Matrix I J (ZMod q)) :
    ∃ (R : Finset I) (C : Finset J),
      span (ZMod q) (M.row '' (R : Set I)) = span _ (Set.range M.row) ∧
      span (ZMod q) (M.col '' (C : Set J)) = span _ (Set.range M.col) ∧
      2^R.card ≤ Nat.card (span (ZMod q) (Set.range M.row)) ∧
      2^C.card ≤ Nat.card (span (ZMod q) (Set.range M.row)) := by
  classical
  obtain ⟨R,_,row,size⟩ := small_generators (R := ZMod q) M.row univ
  obtain ⟨C,_,col,size'⟩ := small_generators (R := ZMod q) M.col univ
  simp only [coe_univ,Set.image_univ] at row col size size'
  have same := row_column_image_card M
  change Nat.card (LinearMap.range M.mulVecLin) = Nat.card (LinearMap.range M.vecMulLinear) at same
  rw [Matrix.range_mulVecLin,range_vecMulLinear] at same
  exact ⟨R,C,row,col,size,size'.trans_eq same⟩

end InducedDegreeRepetition.Restriction
