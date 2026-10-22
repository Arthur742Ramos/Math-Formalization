/- AI-assisted formalization under the repository Apache-2.0 license.
Executable rational weights for the source's original-label two-center bins. -/
module
public import RationalExplicitBinPayoff
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalBinSlotLabel (L : ℕ) (hL : 0 < L) (b : Fin 2) : Fin L :=
  if b.val=0 then
    ⟨(L-1)/2,lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.sub_lt hL (Nat.zero_lt_succ 0))⟩
  else ⟨L/2,Nat.div_lt_self hL (Nat.lt_succ_self 1)⟩

def rationalBinnedLabel {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b) (b : Fin h × Fin 2) :
    Fin (∑ b,L b) := finSigmaFinEquiv ⟨b.1,rationalBinSlotLabel (L b.1) (hL b.1) b.2⟩

def rationalBinnedWeights {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b) (r : ℚ)
    (j : Fin (∑ b,L b)) : ℚ :=
  ∑ b : Fin h × Fin 2, if rationalBinnedLabel L hL b=j then
    (r/((∑ b,L b : ℕ) : ℚ))*(L b.1 : ℚ)/((2 : ℕ) : ℚ) else 0

theorem rational_binned_label_eq {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b)
    (b : Fin h × Fin 2) : rationalBinnedLabel L hL b=binnedLabel L hL b := rfl

theorem rational_binned_weights_real {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b) (r : ℚ)
    (j : Fin (∑ b,L b)) :
    (rationalBinnedWeights L hL r j : ℝ)=binnedWeights L hL (r : ℝ) j := by
  simp only [rationalBinnedWeights,binnedWeights,pushWeights,Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [rational_binned_label_eq]
  by_cases hb : binnedLabel L hL b=j
  · simp only [hb,ite_true,Rat.cast_div,Rat.cast_mul,Rat.cast_natCast]
  · simp only [hb,ite_false,Rat.cast_zero]

theorem rational_binned_weights_nonnegative {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b)
    (r : ℚ) (hr : 0 ≤ r) : ∀ j, 0 ≤ rationalBinnedWeights L hL r j := by
  intro j
  have hh := binned_nonneg L hL (r : ℝ) (by exact_mod_cast hr) j
  rw [←rational_binned_weights_real] at hh
  exact_mod_cast hh

theorem rational_binned_weights_mass {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b, 0 < L b)
    (r : ℚ) (hm : 0 < ∑ b,L b) : (∑ j,rationalBinnedWeights L hL r j)=r := by
  have hh := binned_mass L hL (r : ℝ) hm
  simp_rw [←rational_binned_weights_real] at hh
  exact_mod_cast hh

end SparseCompletion
