/- AI-assisted formalization under the repository Apache-2.0 license.
The explicit same-bin weighted response on the actual original-label program. -/
module
public import ProtectedSources.RationalBinLocalResponse
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem rational_bin_pair_response {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b,0 < L b)
    (i : Fin (∑ b,L b)) (hi : rationalBinRepresentative L i=true) :
    ((L (rationalBinDecode L i).1 : ℚ)/((2 : ℕ) : ℚ))*
      (∑ s : Fin 2,rationalExplicitBinPayoff L i
        (rationalBinnedLabel L hL ((rationalBinDecode L i).1,s)))=
      ((2 : ℕ) : ℚ)*((rationalBinDecode L i).2.val : ℚ)+1-
        (L (rationalBinDecode L i).1 : ℚ) := by
  have hi' : (rationalBinDecode L i).2.val=(L (rationalBinDecode L i).1-1)/2 ∨
      (rationalBinDecode L i).2.val=L (rationalBinDecode L i).1/2 :=
    of_decide_eq_true hi
  have hlocal : (rationalBinDecode L i).2=binLower _ (hL _) ∨
      (rationalBinDecode L i).2=binUpper _ (hL _) := by
    rcases hi' with he | he
    · exact Or.inl (Fin.ext he)
    · exact Or.inr (Fin.ext he)
  have he (s : Fin 2) : rationalExplicitBinPayoff L i
        (rationalBinnedLabel L hL ((rationalBinDecode L i).1,s))=
      rationalCentralPayoff (rationalBinDecode L i).2
        (rationalBinSlotLabel _ (hL _) s) := by
    rw [rationalExplicitBinPayoff,hi,
      rational_binned_label_representative L hL ((rationalBinDecode L i).1,s)]
    simp only [ite_true]
    exact rational_supported_bin_payoff_local L i _
  simp_rw [he]
  rw [Fin.sum_univ_two]
  change ((L (rationalBinDecode L i).1 : ℚ)/((2 : ℕ) : ℚ))*
    (rationalCentralPayoff (rationalBinDecode L i).2 (binLower _ (hL _))+
      rationalCentralPayoff (rationalBinDecode L i).2 (binUpper _ (hL _)))=_
  exact rational_central_pair_response _ (hL _) _ hlocal

end SparseCompletion
