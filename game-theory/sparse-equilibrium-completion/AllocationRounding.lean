/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ValueStability

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def roundedAnchor (s p δ : ℝ) : ℝ := s+δ*(Nat.floor ((p-s)/δ) : ℝ)

theorem rounded_anchor_bounds (s p δ : ℝ) (hsp : s ≤ p) (hδ : 0 < δ) :
    s ≤ roundedAnchor s p δ ∧ roundedAnchor s p δ ≤ p ∧ p-roundedAnchor s p δ < δ := by
  have hx : 0 ≤ (p-s)/δ := div_nonneg (sub_nonneg.mpr hsp) (le_of_lt hδ)
  have h1 := Nat.floor_le hx
  have h2 := Nat.lt_floor_add_one ((p-s)/δ)
  have h3 := (le_div_iff₀ hδ).mp h1
  have h4 := (div_lt_iff₀ hδ).mp h2
  unfold roundedAnchor
  exact ⟨le_add_of_nonneg_right (mul_nonneg (le_of_lt hδ) (Nat.cast_nonneg _)),by nlinarith,by nlinarith⟩

def roundedAllocation {α : Type*} (s p : α → ℝ) (δ : ℝ) (i : α) : ℝ := roundedAnchor (s i) (p i) δ

def removedAnchorMass {α : Type*} [Fintype α] (s p : α → ℝ) (δ : ℝ) : ℝ :=
  ∑ i, (p i-roundedAllocation s p δ i)

theorem removed_anchor_mass_bounds {α : Type*} [Fintype α] (s p : α → ℝ) (δ : ℝ)
    (hsp : ∀ i, s i ≤ p i) (hδ : 0 < δ) :
    0 ≤ removedAnchorMass s p δ ∧ removedAnchorMass s p δ ≤ (Fintype.card α : ℝ)*δ := by
  constructor
  · exact Finset.sum_nonneg fun i _ => sub_nonneg.mpr (rounded_anchor_bounds _ _ _ (hsp i) hδ).2.1
  · calc
      removedAnchorMass s p δ ≤ ∑ _i : α, δ := Finset.sum_le_sum fun i _ =>
        le_of_lt (rounded_anchor_bounds _ _ _ (hsp i) hδ).2.2
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

def transferredResidual {ι : Type*} [DecidableEq ι] (q : ι → ℝ) (d : ℝ) (j : ι) (i : ι) : ℝ :=
  q i+if i=j then d else 0

theorem transferred_residual_mass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (d : ℝ) (j : ι) : (∑ i, transferredResidual q d j i)=(∑ i, q i)+d := by
  simp only [transferredResidual,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem allocation_rounding_mass {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (s p : α → ℝ) (q : ι → ℝ) (δ : ℝ) (j : ι) :
    (∑ i, roundedAllocation s p δ i)+(∑ i, transferredResidual q (removedAnchorMass s p δ) j i)=
      (∑ i, p i)+(∑ i, q i) := by
  rw [transferred_residual_mass]
  unfold removedAnchorMass
  rw [Finset.sum_sub_distrib]
  ring

theorem transferred_residual_distance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (d : ℝ) (j : ι) (hd : 0 ≤ d) :
    (∑ i, |q i-transferredResidual q d j i|)=d := by
  have he : ∀ i, |q i-transferredResidual q d j i|=if i=j then d else 0 := by
    intro i
    by_cases h : i=j
    · simp only [transferredResidual,h,ite_true,sub_add_cancel_left,abs_neg,abs_of_nonneg hd]
    · simp only [transferredResidual,h,ite_false,add_zero,sub_self,abs_zero]
  simp_rw [he]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem allocation_rounding_distance {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (s p : α → ℝ) (q : ι → ℝ) (δ : ℝ) (j : ι)
    (hsp : ∀ i, s i ≤ p i) (hδ : 0 < δ) :
    (∑ a, |blockWeights p q a-
      blockWeights (roundedAllocation s p δ) (transferredResidual q (removedAnchorMass s p δ) j) a|) ≤
        (2 : ℕ)*(Fintype.card α : ℝ)*δ := by
  have hd := removed_anchor_mass_bounds s p δ hsp hδ
  have ha : (∑ i, |p i-roundedAllocation s p δ i|)=removedAnchorMass s p δ := by
    apply Finset.sum_congr rfl
    intro i _
    exact abs_of_nonneg (sub_nonneg.mpr (rounded_anchor_bounds _ _ _ (hsp i) hδ).2.1)
  rw [Fintype.sum_sum_type]
  simp only [blockWeights,Sum.elim_inl,Sum.elim_inr]
  rw [ha,transferred_residual_distance q _ j hd.1]
  norm_num only [Nat.cast_ofNat]
  linarith

end
end SparseCompletion
