/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.BinnedMoments

@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem bin_middle_even_gap (L : ℕ) (hL : 0 < L) (heven : L%(2 : ℕ)=0) :
    (binLower L hL).val+1=(binUpper L hL).val := by
  simp only [binLower,binUpper]
  omega

theorem bin_middle_odd_same (L : ℕ) (hL : 0 < L) (hodd : L%(2 : ℕ)≠0) :
    binLower L hL=binUpper L hL := by
  apply Fin.ext
  simp only [binLower,binUpper]
  omega

theorem bin_quadratic_parity_identity (L : ℕ) (hL : 0 < L) (a d : ℝ) :
    (∑ i : Fin L, (a+d*i.val)^(2 : ℕ))-
      (∑ i, binCompressedWeights L hL i*(a+d*i.val)^(2 : ℕ))=
      d^(2 : ℕ)*(L : ℝ)/(12 : ℕ)*((L : ℝ)^(2 : ℕ)-(if L%(2 : ℕ)=0 then (4 : ℕ) else 1)) := by
  norm_num only [Nat.cast_ofNat] at *
  rw [bin_compressed_moment,bin_quadratic_loss_identity]
  by_cases heven : L%2=0
  · rw [ite_eq_left heven]
    have hh : ((binUpper L hL).val : ℝ)=(binLower L hL).val+1 := by
      exact_mod_cast (bin_middle_even_gap L hL heven).symm
    rw [hh]
    ring
  · rw [ite_eq_right heven,bin_middle_odd_same L hL heven]
    ring

theorem bin_odd_support (L : ℕ) (hL : 0 < L) (hodd : L%(2 : ℕ)≠0) :
    (Finset.univ.filter fun i => binCompressedWeights L hL i ≠ 0).card ≤ 1 := by
  classical
  have hsup : (Finset.univ.filter fun i => binCompressedWeights L hL i ≠ 0) ⊆
      {binLower L hL} := by
    intro i hi
    have hn := (Finset.mem_filter.mp hi).2
    by_contra he
    have heq : ∀ b : Fin 2, binCompressedLabel L hL b=binLower L hL := by
      intro b
      simp only [binCompressedLabel,←bin_middle_odd_same L hL hodd,ite_self]
    have hz : binCompressedWeights L hL i=0 := by
      unfold binCompressedWeights pushWeights
      apply Finset.sum_eq_zero
      intro b _
      have hne : binCompressedLabel L hL b ≠ i := by
        rw [heq]
        simpa only [Finset.mem_singleton,ne_comm] using he
      simp only [ite_eq_right hne]
    exact hn hz
  exact le_trans (Finset.card_le_card hsup) (by simp)

end
end SparseCompletion
