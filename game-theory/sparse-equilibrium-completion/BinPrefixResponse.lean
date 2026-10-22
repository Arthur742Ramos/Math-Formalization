/- AI-assisted formalization under the repository Apache-2.0 license.
Source explicit cross-bin response on the original ordered partition. -/
module
public import BinnedWitness
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem bin_prefix_mass (h : ℕ) (L : Fin h → ℕ) (b : Fin h) :
    prefixMass (fun c => (L c : ℝ)) b.val=(binStart L b : ℝ) := by
  unfold prefixMass binStart
  rw [Nat.cast_sum]
  apply Finset.sum_bij (fun i hi =>
    (⟨i.val,(Finset.mem_filter.mp hi).2⟩ : Fin b.val))
  · intro i _
    exact Finset.mem_univ _
  · intro i hi j hj he
    exact Fin.ext (congrArg (fun a : Fin b.val => a.val) he)
  · intro j _
    refine ⟨Fin.castLE b.isLt.le j,?_,rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,j.isLt⟩
  · intro i hi
    have he : Fin.castLE b.isLt.le
        (⟨i.val,(Finset.mem_filter.mp hi).2⟩ : Fin b.val)=i := Fin.ext rfl
    rw [he]

theorem bin_ordered_response (h : ℕ) (L : Fin h → ℕ) (b : Fin h) :
    response (orderedBlock 1) (fun c => (L c : ℝ)) b=
      ((2 : ℕ) : ℝ)*(binStart L b : ℝ)+(L b : ℝ)-((∑ c,L c : ℕ) : ℝ) := by
  rw [orderedBlock_response _ ((∑ c,L c : ℕ) : ℝ) (by simp only [Nat.cast_sum])]
  unfold targetScore
  rw [bin_prefix_mass]
  ring

end
end SparseCompletion
