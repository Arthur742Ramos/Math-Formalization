/- AI-assisted formalization under the repository Apache-2.0 license.
Source explicit even-bin payoff: two central representatives exchange opposite 2/L payoffs. -/
module
public import BinCompression
@[expose] public section
namespace SparseCompletion

def rationalCentralPayoff {L : ℕ} (i j : Fin L) : ℚ :=
  if i.val < j.val then -(((2 : ℕ) : ℚ)/(L : ℚ))
  else if j.val < i.val then ((2 : ℕ) : ℚ)/(L : ℚ) else 0

theorem rational_central_payoff_diagonal {L : ℕ} (i : Fin L) :
    rationalCentralPayoff i i=0 := by
  simp only [rationalCentralPayoff,lt_self_iff_false,ite_false]

theorem rational_central_payoff_skew {L : ℕ} (i j : Fin L) :
    rationalCentralPayoff i j= -rationalCentralPayoff j i := by
  by_cases hij : i.val < j.val
  · have hji : ¬j.val < i.val := by omega
    simp only [rationalCentralPayoff,hij,hji,ite_true,ite_false]
  · by_cases hji : j.val < i.val
    · simp only [rationalCentralPayoff,hij,hji,ite_true,ite_false,neg_neg]
    · simp only [rationalCentralPayoff,hij,hji,ite_false,neg_zero]

theorem rational_central_payoff_bounds {L : ℕ} (i j : Fin L) :
    -1 ≤ rationalCentralPayoff i j ∧ rationalCentralPayoff i j ≤ 1 := by
  by_cases hij : i.val=j.val
  · have he : i=j := Fin.ext hij
    subst j
    rw [rational_central_payoff_diagonal]
    norm_num
  · have hL : (2 : ℕ) ≤ L := by have hi := i.isLt; have hj := j.isLt; omega
    have hLQ : ((2 : ℕ) : ℚ) ≤ (L : ℚ) := by exact_mod_cast hL
    have hpos : (0 : ℚ) < (L : ℚ) := by exact_mod_cast (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hL)
    have hb : (0 : ℚ) ≤ ((2 : ℕ) : ℚ)/(L : ℚ) ∧ ((2 : ℕ) : ℚ)/(L : ℚ) ≤ 1 :=
      ⟨div_nonneg (by norm_num) hpos.le,(div_le_one hpos).mpr hLQ⟩
    unfold rationalCentralPayoff
    split_ifs <;> constructor <;> linarith

/-- The odd-bin duplicate is one label and has zero diagonal. Distinct central
representatives exchange exactly the source payoff, rather than unit payoff. -/
theorem rational_central_pair_response (L : ℕ) (hL : 0 < L) (i : Fin L)
    (hi : i=binLower L hL ∨ i=binUpper L hL) :
    ((L : ℚ)/((2 : ℕ) : ℚ))*
      (rationalCentralPayoff i (binLower L hL)+rationalCentralPayoff i (binUpper L hL))=
        ((2 : ℕ) : ℚ)*(i.val : ℚ)+1-(L : ℚ) := by
  have hsum := bin_middle_sum L hL
  have hord := bin_middle_order L hL
  have hLQ : (L : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hL)
  by_cases he : binLower L hL=binUpper L hL
  · have hcenter : (2 : ℕ)*(binLower L hL).val+1=L := by
      have hp := congrArg Fin.val he
      simp only [binLower,binUpper] at hp ⊢
      omega
    rcases hi with rfl | rfl
    · rw [←he,rational_central_payoff_diagonal]
      have hQ : ((2 : ℕ) : ℚ)*((binLower L hL).val : ℚ)+1=(L : ℚ) := by exact_mod_cast hcenter
      simp only [add_zero,mul_zero]
      linarith
    · rw [←he,rational_central_payoff_diagonal]
      have hQ : ((2 : ℕ) : ℚ)*((binLower L hL).val : ℚ)+1=(L : ℚ) := by exact_mod_cast hcenter
      simp only [add_zero,mul_zero]
      linarith
  · have hlt : (binLower L hL).val < (binUpper L hL).val := by
      have hn : (binLower L hL).val ≠ (binUpper L hL).val := fun h => he (Fin.ext h)
      exact lt_of_le_of_ne hord hn
    have hnot : ¬(binUpper L hL).val < (binLower L hL).val := by omega
    have hl : (2 : ℕ)*(binLower L hL).val+2=L := by simp only [binLower,binUpper] at hlt ⊢; omega
    have hu : (2 : ℕ)*(binUpper L hL).val=L := by simp only [binLower,binUpper] at hlt ⊢; omega
    rcases hi with rfl | rfl
    · have hQ : ((2 : ℕ) : ℚ)*((binLower L hL).val : ℚ)+2=(L : ℚ) := by exact_mod_cast hl
      simp only [rationalCentralPayoff,lt_self_iff_false,hlt,hnot,ite_true,ite_false,zero_add]
      field_simp [hLQ]
      nlinarith
    · have hQ : ((2 : ℕ) : ℚ)*((binUpper L hL).val : ℚ)=(L : ℚ) := by exact_mod_cast hu
      simp only [rationalCentralPayoff,lt_self_iff_false,hlt,hnot,ite_true,ite_false,add_zero]
      field_simp [hLQ]
      nlinarith

end SparseCompletion
