/- AI-assisted formalization under the repository Apache-2.0 license. -/
module
public import RationalBinLocalResponse
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem rational_binned_moment {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b,0 < L b)
    (r : ℚ) (f : Fin (∑ b,L b) → ℚ) :
    (∑ j,rationalBinnedWeights L hL r j*f j)=
      (r/((∑ b,L b : ℕ) : ℚ))*∑ b,
        ((L b : ℚ)/((2 : ℕ) : ℚ))*(∑ s : Fin 2,f (rationalBinnedLabel L hL (b,s))) := by
  simp only [rationalBinnedWeights,Finset.sum_mul]
  rw [Finset.sum_comm]
  have he : (∑ b : Fin h × Fin 2,
      ∑ j,(if rationalBinnedLabel L hL b=j then
        (r/((∑ b,L b : ℕ) : ℚ))*(L b.1 : ℚ)/((2 : ℕ) : ℚ) else 0)*f j)=
      ∑ b : Fin h × Fin 2,
        ((r/((∑ b,L b : ℕ) : ℚ))*(L b.1 : ℚ)/((2 : ℕ) : ℚ))*f (rationalBinnedLabel L hL b) := by
    apply Finset.sum_congr rfl
    intro b _
    simp only [ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  rw [he,Fintype.sum_prod_type,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

end SparseCompletion
