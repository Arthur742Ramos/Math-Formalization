/- AI-assisted formalization under the repository Apache-2.0 license. -/
module
public import ProtectedSources.RationalBinPairResponse
public import ProtectedSources.BinPrefixResponse
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalBinSign {h : ℕ} (b c : Fin h) : ℚ :=
  if b.val < c.val then -1 else if c.val < b.val then 1 else 0

theorem rational_bin_sign_real {h : ℕ} (b c : Fin h) :
    (rationalBinSign b c : ℝ)=orderedBlock 1 b c := by
  unfold rationalBinSign orderedBlock
  by_cases hb : b.val < c.val
  · have hh : b < c := hb
    simp only [hb,hh,ite_true,Rat.cast_neg,Rat.cast_one]
  · have hh : ¬b < c := hb
    by_cases hc : c.val < b.val
    · have hc' : c < b := hc
      simp only [hb,hh,hc,hc',ite_false,ite_true,Rat.cast_one]
    · have hc' : ¬c < b := hc
      simp only [hb,hh,hc,hc',ite_false,Rat.cast_zero]

theorem rational_bin_cross_response {h : ℕ} (L : Fin h → ℕ) (b : Fin h) :
    (∑ c,rationalBinSign b c*(L c : ℚ))=
      ((2 : ℕ) : ℚ)*(binStart L b : ℚ)+(L b : ℚ)-((∑ c,L c : ℕ) : ℚ) := by
  have hh := bin_ordered_response h L b
  have he : (∑ c, (rationalBinSign b c : ℝ)*(L c : ℝ))=
      response (orderedBlock 1) (fun c => (L c : ℝ)) b := by
    simp_rw [rational_bin_sign_real]
    rfl
  rw [←he] at hh
  exact_mod_cast hh

theorem rational_bin_other_payoff {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b,0 < L b)
    (i : Fin (∑ b,L b)) (hi : rationalBinRepresentative L i=true)
    (b : Fin h) (hb : b ≠ (rationalBinDecode L i).1) (s : Fin 2) :
    rationalExplicitBinPayoff L i (rationalBinnedLabel L hL (b,s))=
      rationalBinSign (rationalBinDecode L i).1 b := by
  rw [rationalExplicitBinPayoff,hi,rational_binned_label_representative L hL (b,s)]
  simp only [ite_true]
  unfold rationalSupportedBinPayoff rationalBinSign
  rw [rational_binned_label_decode]
  by_cases hlo : (rationalBinDecode L i).1.val < b.val
  · simp only [hlo,ite_true]
  · have hhi : b.val < (rationalBinDecode L i).1.val := by
      have he : b.val ≠ (rationalBinDecode L i).1.val := fun he => hb (Fin.ext he)
      omega
    simp only [hlo,hhi,ite_false,ite_true]

end SparseCompletion
