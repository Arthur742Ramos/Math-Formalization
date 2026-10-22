/- AI-assisted formalization under the repository Apache-2.0 license.
The executed rational matrix is a literal real completion for all real masses. -/
module
public import RationalBinnedResponse
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def explicitBinnedMatrix {h : ℕ} (L : Fin h → ℕ) (i j : Fin (∑ b,L b)) : ℝ :=
  (rationalExplicitBinPayoff L i j : ℝ)

theorem explicit_binned_matrix_skew {h : ℕ} (L : Fin h → ℕ) :
    IsSkew (explicitBinnedMatrix L) := by
  intro i j
  change (rationalExplicitBinPayoff L i j : ℝ)= -(rationalExplicitBinPayoff L j i : ℝ)
  exact_mod_cast rational_explicit_bin_payoff_skew L i j

theorem explicit_binned_matrix_bounds {h : ℕ} (L : Fin h → ℕ)
    (i j : Fin (∑ b,L b)) : -1 ≤ explicitBinnedMatrix L i j ∧ explicitBinnedMatrix L i j ≤ 1 := by
  change -(1 : ℝ) ≤ (rationalExplicitBinPayoff L i j : ℝ) ∧
    (rationalExplicitBinPayoff L i j : ℝ) ≤ 1
  exact_mod_cast rational_explicit_bin_payoff_bounds L i j

theorem rational_binned_response_real {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b,0 < L b)
    (r : ℚ) (hm : 0 < ∑ b,L b) (i : Fin (∑ b,L b)) :
    targetScore (uniformTarget (∑ b,L b) (r : ℝ)) (r : ℝ) i+
      response (explicitBinnedMatrix L) (binnedWeights L hL (r : ℝ)) i=0 := by
  have hh : ((rationalUniformScore r i+
      (∑ j,rationalExplicitBinPayoff L i j*rationalBinnedWeights L hL r j) : ℚ) : ℝ)=0 := by
    exact_mod_cast rational_binned_residual_response L hL r hm i
  simp only [Rat.cast_add,Rat.cast_sum,Rat.cast_mul,rational_uniform_score_real hm,
    rational_binned_weights_real] at hh
  exact hh

theorem binned_weights_linear {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b,0 < L b)
    (r : ℝ) (j : Fin (∑ b,L b)) : binnedWeights L hL r j=r*binnedWeights L hL 1 j := by
  unfold binnedWeights pushWeights
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : binnedLabel L hL b=j
  · simp only [hb,ite_true]
    ring
  · simp only [hb,ite_false,mul_zero]

theorem explicit_binned_residual_response {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b,0 < L b)
    (r : ℝ) (hm : 0 < ∑ b,L b) (i : Fin (∑ b,L b)) :
    targetScore (uniformTarget (∑ b,L b) r) r i+
      response (explicitBinnedMatrix L) (binnedWeights L hL r) i=0 := by
  have hunit := rational_binned_response_real L hL 1 hm i
  simp only [Rat.cast_one] at hunit
  have ht : targetScore (uniformTarget (∑ b,L b) r) r i=
      r*targetScore (uniformTarget (∑ b,L b) 1) 1 i := by
    rw [uniform_target_score,uniform_target_score]
    ring
  rw [ht]
  simp only [response]
  simp_rw [binned_weights_linear L hL r]
  have he : (∑ j,explicitBinnedMatrix L i j*(r*binnedWeights L hL 1 j))=
      r*∑ j,explicitBinnedMatrix L i j*binnedWeights L hL 1 j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he,←mul_add]
  change r*(targetScore (uniformTarget (∑ b,L b) 1) 1 i+
    response (explicitBinnedMatrix L) (binnedWeights L hL 1) i)=0
  rw [hunit,mul_zero]

end
end SparseCompletion
