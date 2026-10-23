/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.IntervalLossMaximum

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem interval_loss_reverse (M lo hi : ℝ) :
    intervalLoss M (-hi) (-lo)=intervalLoss M lo hi := by
  unfold intervalLoss
  have h1 : M- -lo=M+lo := by ring
  have h2 : M+ -hi=M-hi := by ring
  rw [h1,h2]
  exact max_comm _ _

def orderedResidualLossValues {ι : Type*} [Fintype ι] [LinearOrder ι]
    (lo hi : ι → ι → ℝ) (M : ℝ) : Finset ℝ := by
  classical
  exact insert 0 ((Finset.univ.filter fun ij : ι × ι => ij.1 < ij.2).image
    fun ij => intervalLoss M (lo ij.1 ij.2) (hi ij.1 ij.2))

theorem ordered_loss_values_nonempty {ι : Type*} [Fintype ι] [LinearOrder ι]
    (lo hi : ι → ι → ℝ) (M : ℝ) : (orderedResidualLossValues lo hi M).Nonempty := by
  classical
  unfold orderedResidualLossValues
  exact ⟨0,Finset.mem_insert_self _ _⟩

def orderedResidualLossBound {ι : Type*} [Fintype ι] [LinearOrder ι]
    (lo hi : ι → ι → ℝ) (M : ℝ) : ℝ :=
  (orderedResidualLossValues lo hi M).max' (ordered_loss_values_nonempty lo hi M)

theorem residual_loss_values_ordered {ι : Type*} [Fintype ι] [LinearOrder ι]
    (lo hi : ι → ι → ℝ) (M : ℝ)
    (hrev : ∀ i j, i ≠ j → lo i j= -hi j i ∧ hi i j= -lo j i) :
    residualLossValues lo hi M=orderedResidualLossValues lo hi M := by
  classical
  ext z
  simp only [residualLossValues,orderedResidualLossValues,Finset.mem_insert,Finset.mem_image,
    Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro (rfl | ⟨⟨i,j⟩,hij,hz⟩)
    · exact Or.inl rfl
    · apply Or.inr
      rcases lt_or_gt_of_ne hij with h | h
      · exact ⟨(i,j),h,hz⟩
      · refine ⟨(j,i),h,?_⟩
        have hs : intervalLoss M (lo i j) (hi i j)=intervalLoss M (lo j i) (hi j i) := by
          rw [(hrev i j hij).1,(hrev i j hij).2,interval_loss_reverse]
        exact hs.symm.trans hz
  · rintro (rfl | ⟨⟨i,j⟩,hij,hz⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨(i,j),ne_of_lt hij,hz⟩

theorem residual_loss_bound_ordered {ι : Type*} [Fintype ι] [LinearOrder ι]
    (lo hi : ι → ι → ℝ) (M : ℝ)
    (hrev : ∀ i j, i ≠ j → lo i j= -hi j i ∧ hi i j= -lo j i) :
    residualLossBound lo hi M=orderedResidualLossBound lo hi M := by
  unfold residualLossBound orderedResidualLossBound
  have hs := residual_loss_values_ordered lo hi M hrev
  apply le_antisymm
  · apply Finset.max'_le
    intro x hx
    exact Finset.le_max' _ _ (hs ▸ hx)
  · apply Finset.max'_le
    intro x hx
    exact Finset.le_max' _ _ (hs.symm ▸ hx)

end
end SparseCompletion
