module

public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Tactic.Linarith

public section
namespace InducedDegreeRepetition.Restriction

open Finset Submodule
open scoped Classical
variable {I M R : Type*} [Ring R] [AddCommGroup M] [Module R M] [Finite M]

/-- Strict enlargement of a finite submodule at least doubles its size. -/
theorem double_of_lt {H K : Submodule R M} (hlt : H < K) : 2*Nat.card H ≤ Nat.card K := by
  let A := H.toAddSubgroup
  let B := K.toAddSubgroup
  have ab : A ≤ B := hlt.le
  have size := A.relIndex_mul_card B
  rw [inf_eq_left.mpr ab] at size
  have p : A.relIndex B ≠ 0 := by
    intro hz
    rw [hz,zero_mul] at size
    exact Nat.card_pos.ne' size.symm
  have n : A.relIndex B ≠ 1 := fun eq => hlt.not_ge (AddSubgroup.relIndex_eq_one.mp eq)
  exact (Nat.mul_le_mul_right (Nat.card A) (by omega : 2 ≤ A.relIndex B)).trans_eq size

/-- An actual subfamily generates the entire span with at most log₂ of its size
many generators. This uses additive indices and applies over composite moduli. -/
theorem small_generators (v : I → M) (T : Finset I) :
    ∃ S ⊆ T, span R (v '' (S : Set I)) = span R (v '' (T : Set I)) ∧
      2^S.card ≤ Nat.card (span R (v '' (T : Set I))) := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨∅,Subset.rfl,rfl,by simp⟩
  | @insert i T hi ih =>
    obtain ⟨S,sub,eq,size⟩ := ih
    simp only [coe_insert,Set.image_insert_eq]
    by_cases mem : v i ∈ span R (v '' (T : Set I))
    · rw [span_insert_eq_span mem]
      exact ⟨S,sub.trans (subset_insert ..),eq,size⟩
    · let H := span R (v '' (T : Set I))
      let K := span R (insert (v i) (v '' (T : Set I)))
      have lt : H < K := lt_of_le_of_ne (span_mono (Set.subset_insert ..)) fun eq' => by
        have m : v i ∈ K := subset_span (Set.mem_insert ..)
        rw [← eq'] at m
        exact mem m
      refine ⟨insert i S,insert_subset_insert i sub,?_,?_⟩
      · simp only [coe_insert,Set.image_insert_eq,span_insert,eq]
      · rw [card_insert_of_notMem (fun h => hi (sub h)),pow_succ,mul_comm]
        exact (Nat.mul_le_mul_left 2 size).trans (double_of_lt lt)

end InducedDegreeRepetition.Restriction
