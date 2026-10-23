/- AI-assisted formalization under the repository Apache-2.0 license.
Same-bin source payoffs agree with the central-pair calculation. -/
module
public import ProtectedSources.RationalBinnedOmitted
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem rational_binned_label_decode {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b,0 < L b)
    (b : Fin h × Fin 2) :
    rationalBinDecode L (rationalBinnedLabel L hL b)=
      ⟨b.1,rationalBinSlotLabel (L b.1) (hL b.1) b.2⟩ :=
  finSigmaFinEquiv.symm_apply_apply _

theorem rational_supported_bin_payoff_local {h : ℕ} (L : Fin h → ℕ)
    (i : Fin (∑ b,L b)) (j : Fin (L (rationalBinDecode L i).1)) :
    rationalSupportedBinPayoff L i (finSigmaFinEquiv ⟨(rationalBinDecode L i).1,j⟩)=
      rationalCentralPayoff (rationalBinDecode L i).2 j := by
  have hd : rationalBinDecode L (finSigmaFinEquiv ⟨(rationalBinDecode L i).1,j⟩)=
      ⟨(rationalBinDecode L i).1,j⟩ := finSigmaFinEquiv.symm_apply_apply _
  have hv := rational_bin_decode_val L i
  have hj := finSigmaFinEquiv_apply (⟨(rationalBinDecode L i).1,j⟩ : (b : Fin h) × Fin (L b))
  change (finSigmaFinEquiv ⟨(rationalBinDecode L i).1,j⟩).val=
    binStart L (rationalBinDecode L i).1+j.val at hj
  have hlo : i.val < (finSigmaFinEquiv ⟨(rationalBinDecode L i).1,j⟩).val ↔
      (rationalBinDecode L i).2.val < j.val := by omega
  have hhi : (finSigmaFinEquiv ⟨(rationalBinDecode L i).1,j⟩).val < i.val ↔
      j.val < (rationalBinDecode L i).2.val := by omega
  simp only [rationalSupportedBinPayoff,hd,lt_self_iff_false,ite_false,hlo,hhi,rationalCentralPayoff]

end SparseCompletion
