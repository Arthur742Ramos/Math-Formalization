/- AI-assisted formalization under the repository Apache-2.0 license.
Exact responses of the source-explicit rational bin payoff program. -/
module
public import ProtectedSources.RationalBinCrossResponse
public import ProtectedSources.RationalBinnedMoment
public import ProtectedSources.RationalUniformScore
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

theorem rational_binned_supported_response {h : ℕ}
    (L : Fin h → ℕ) (hL : ∀ b,0 < L b) (r : ℚ)
    (i : Fin (∑ b,L b)) (hi : rationalBinRepresentative L i=true) :
    rationalUniformScore r i+
      (∑ j,rationalExplicitBinPayoff L i j*rationalBinnedWeights L hL r j)=0 := by
  let a := (rationalBinDecode L i).1
  let C := ((2 : ℕ) : ℚ)*((rationalBinDecode L i).2.val : ℚ)+1-(L a : ℚ)
  have hbin (b : Fin h) : ((L b : ℚ)/((2 : ℕ) : ℚ))*
      (∑ s : Fin 2,rationalExplicitBinPayoff L i (rationalBinnedLabel L hL (b,s)))=
      rationalBinSign a b*(L b : ℚ)+(if b=a then C else 0) := by
    by_cases hb : b=a
    · subst b
      rw [rational_bin_pair_response L hL i hi]
      simp only [rationalBinSign,lt_self_iff_false,ite_false,ite_true,zero_mul,zero_add]
      rfl
    · have he (s : Fin 2) := rational_bin_other_payoff L hL i hi b hb s
      simp_rw [he]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,hb,ite_false,add_zero]
      ring
  have hresp : (∑ j,rationalExplicitBinPayoff L i j*rationalBinnedWeights L hL r j)=
      (r/((∑ b,L b : ℕ) : ℚ))*∑ b,
        ((L b : ℚ)/((2 : ℕ) : ℚ))*(∑ s : Fin 2,
          rationalExplicitBinPayoff L i (rationalBinnedLabel L hL (b,s))) := by
    simpa only [mul_comm] using rational_binned_moment L hL r (rationalExplicitBinPayoff L i)
  rw [hresp]
  simp_rw [hbin]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [rational_bin_cross_response]
  have hv : (i.val : ℚ)=(binStart L a : ℚ)+((rationalBinDecode L i).2.val : ℚ) := by
    exact_mod_cast rational_bin_decode_val L i
  unfold rationalUniformScore
  dsimp only [C]
  rw [hv]
  ring

theorem rational_binned_residual_response {h : ℕ}
    (L : Fin h → ℕ) (hL : ∀ b,0 < L b) (r : ℚ) (hm : 0 < ∑ b,L b)
    (i : Fin (∑ b,L b)) :
    rationalUniformScore r i+
      (∑ j,rationalExplicitBinPayoff L i j*rationalBinnedWeights L hL r j)=0 := by
  cases hi : rationalBinRepresentative L i
  · exact rational_binned_omitted_response L hL r hm i hi
  · exact rational_binned_supported_response L hL r i hi

theorem rational_binned_explicit_completion {h : ℕ}
    (L : Fin h → ℕ) (hL : ∀ b,0 < L b) (r : ℚ) (hr : 0 ≤ r) (hm : 0 < ∑ b,L b) :
    (∀ i,0 ≤ rationalBinnedWeights L hL r i) ∧ (∑ i,rationalBinnedWeights L hL r i)=r ∧
    (∀ i j,rationalExplicitBinPayoff L i j= -rationalExplicitBinPayoff L j i) ∧
    (∀ i j,-1 ≤ rationalExplicitBinPayoff L i j ∧ rationalExplicitBinPayoff L i j ≤ 1) ∧
    ∀ i,rationalUniformScore r i+
      (∑ j,rationalExplicitBinPayoff L i j*rationalBinnedWeights L hL r j)=0 :=
  ⟨rational_binned_weights_nonnegative L hL r hr,rational_binned_weights_mass L hL r hm,
    rational_explicit_bin_payoff_skew L,rational_explicit_bin_payoff_bounds L,
    rational_binned_residual_response L hL r hm⟩

end SparseCompletion
