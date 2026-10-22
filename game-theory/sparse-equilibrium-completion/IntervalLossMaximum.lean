/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import IntervalProjection

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem interval_loss_bounds (M lo hi : ℝ) (hlo : -M ≤ lo) (hhi : hi ≤ M) (hlu : lo ≤ hi) :
    0 ≤ intervalLoss M lo hi ∧ intervalLoss M lo hi ≤ (2 : ℕ)*M := by
  refine ⟨interval_loss_nonnegative M lo hi hlo,?_⟩
  unfold intervalLoss
  norm_num only [Nat.cast_ofNat]
  exact max_le (by nlinarith) (by nlinarith)

theorem interval_loss_zero_iff (M lo hi : ℝ) (hlo : -M ≤ lo) (hhi : hi ≤ M) :
    intervalLoss M lo hi=0 ↔ lo= -M ∧ hi=M := by
  constructor
  · intro h
    have h0 : M+lo ≤ 0 := by rw [←h]; exact le_max_left _ _
    have h1 : M-hi ≤ 0 := by rw [←h]; exact le_max_right _ _
    constructor <;> linarith
  · rintro ⟨rfl,rfl⟩
    simp only [intervalLoss,add_neg_cancel,sub_self,max_self]

def residualLossValues {ι : Type*} [Fintype ι] (lo hi : ι → ι → ℝ) (M : ℝ) : Finset ℝ := by
  classical
  exact insert 0 ((Finset.univ.filter fun ij : ι × ι => ij.1 ≠ ij.2).image
    fun ij => intervalLoss M (lo ij.1 ij.2) (hi ij.1 ij.2))

theorem residual_loss_values_nonempty {ι : Type*} [Fintype ι] (lo hi : ι → ι → ℝ) (M : ℝ) :
    (residualLossValues lo hi M).Nonempty := by
  classical
  unfold residualLossValues
  exact ⟨0,Finset.mem_insert_self _ _⟩

def residualLossBound {ι : Type*} [Fintype ι] (lo hi : ι → ι → ℝ) (M : ℝ) : ℝ :=
  (residualLossValues lo hi M).max' (residual_loss_values_nonempty lo hi M)

theorem residual_loss_bound_nonnegative {ι : Type*} [Fintype ι] (lo hi : ι → ι → ℝ) (M : ℝ) :
    0 ≤ residualLossBound lo hi M := by
  classical
  unfold residualLossBound
  apply Finset.le_max'
  unfold residualLossValues
  exact Finset.mem_insert_self _ _

theorem residual_loss_le_bound {ι : Type*} [Fintype ι] (lo hi : ι → ι → ℝ) (M : ℝ)
    (i j : ι) (hij : i ≠ j) : intervalLoss M (lo i j) (hi i j) ≤ residualLossBound lo hi M := by
  classical
  unfold residualLossBound
  apply Finset.le_max'
  unfold residualLossValues
  apply Finset.mem_insert_of_mem
  apply Finset.mem_image.mpr
  exact ⟨(i,j),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hij⟩,rfl⟩

theorem residual_loss_bound_le {ι : Type*} [Fintype ι] (lo hi : ι → ι → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hlo : ∀ i j, i ≠ j → -M ≤ lo i j)
    (hhi : ∀ i j, i ≠ j → hi i j ≤ M) (hlu : ∀ i j, i ≠ j → lo i j ≤ hi i j) :
    residualLossBound lo hi M ≤ (2 : ℕ)*M := by
  classical
  unfold residualLossBound
  apply Finset.max'_le
  intro x hx
  unfold residualLossValues at hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · positivity
  · obtain ⟨⟨i,j⟩,hij,rfl⟩ := Finset.mem_image.mp hx
    have he := (Finset.mem_filter.mp hij).2
    exact (interval_loss_bounds M (lo i j) (hi i j) (hlo i j he) (hhi i j he) (hlu i j he)).2

theorem residual_loss_bound_le_iff {ι : Type*} [Fintype ι] (lo hi : ι → ι → ℝ) (M β : ℝ) :
    residualLossBound lo hi M ≤ β ↔ 0 ≤ β ∧
      ∀ i j, i ≠ j → intervalLoss M (lo i j) (hi i j) ≤ β := by
  classical
  constructor
  · intro h
    exact ⟨le_trans (residual_loss_bound_nonnegative lo hi M) h,
      fun i j hij => le_trans (residual_loss_le_bound lo hi M i j hij) h⟩
  · rintro ⟨hβ,h⟩
    unfold residualLossBound
    apply Finset.max'_le
    intro x hx
    unfold residualLossValues at hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hβ
    · obtain ⟨⟨i,j⟩,hij,rfl⟩ := Finset.mem_image.mp hx
      exact h i j (Finset.mem_filter.mp hij).2

theorem residual_loss_bound_zero_iff {ι : Type*} [Fintype ι] (lo hi : ι → ι → ℝ) (M : ℝ)
    (hlo : ∀ i j, i ≠ j → -M ≤ lo i j) (hhi : ∀ i j, i ≠ j → hi i j ≤ M) :
    residualLossBound lo hi M=0 ↔ ∀ i j, i ≠ j → lo i j= -M ∧ hi i j=M := by
  constructor
  · intro h i j hij
    apply (interval_loss_zero_iff M _ _ (hlo i j hij) (hhi i j hij)).mp
    apply le_antisymm
    · rw [←h]
      exact residual_loss_le_bound lo hi M i j hij
    · exact interval_loss_nonnegative M _ _ (hlo i j hij)
  · intro h
    apply le_antisymm
    · apply (residual_loss_bound_le_iff lo hi M 0).mpr
      refine ⟨le_refl _,?_⟩
      intro i j hij
      have hz := (interval_loss_zero_iff M _ _ (hlo i j hij) (hhi i j hij)).mpr (h i j hij)
      exact le_of_eq hz
    · exact residual_loss_bound_nonnegative lo hi M

end
end SparseCompletion
