/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import AllocationRounding

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem response_strategy_distance {ν : Type*} [Fintype ν]
    (A : ν → ν → ℝ) (x y : ν → ℝ) (M : ℝ)
    (hA : ∀ i j, |A i j| ≤ M) (i : ν) :
    |response A x i-response A y i| ≤ M*(∑ j, |x j-y j|) := by
  calc
    |response A x i-response A y i| = |∑ j, A i j*(x j-y j)| := by
      simp only [response,mul_sub,Finset.sum_sub_distrib]
    _ ≤ ∑ j, |A i j*(x j-y j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, M*|x j-y j| := Finset.sum_le_sum fun j _ => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hA i j) (abs_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem exploitability_strategy_distance {ν : Type*} [Fintype ν] [Nonempty ν]
    (A : ν → ν → ℝ) (x y : ν → ℝ) (M : ℝ)
    (hA : ∀ i j, |A i j| ≤ M) :
    |exploitability A x-exploitability A y| ≤ M*(∑ j, |x j-y j|) := by
  have hone : ∀ x y : ν → ℝ, exploitability A x ≤ exploitability A y+M*(∑ j, |x j-y j|) := by
    intro x y
    apply (exploitability_le_iff A x _).mpr
    intro i
    have h := (abs_le.mp (response_strategy_distance A x y M hA i)).2
    linarith [response_le_exploitability A y i]
  apply abs_le.mpr
  constructor
  · have hh := hone y x
    simp_rw [abs_sub_comm (y _) (x _)] at hh
    linarith
  · linarith [hone x y]

theorem allocation_rounding_value_bound {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι] [Nonempty (α ⊕ ι)]
    (s p : α → ℝ) (q : ι → ℝ) (δ M : ℝ) (j : ι)
    (A : (α ⊕ ι) → (α ⊕ ι) → ℝ)
    (hsp : ∀ i, s i ≤ p i) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hA : ∀ i j, |A i j| ≤ M) :
    exploitability A (blockWeights (roundedAllocation s p δ)
      (transferredResidual q (removedAnchorMass s p δ) j)) ≤
      exploitability A (blockWeights p q)+(2 : ℕ)*M*(Fintype.card α : ℝ)*δ := by
  have h := (abs_le.mp (exploitability_strategy_distance A (blockWeights p q)
    (blockWeights (roundedAllocation s p δ) (transferredResidual q (removedAnchorMass s p δ) j)) M hA)).1
  have hd := mul_le_mul_of_nonneg_left (allocation_rounding_distance s p q δ j hsp hδ) hM
  norm_num only [Nat.cast_ofNat] at hd ⊢
  nlinarith

end
end SparseCompletion
