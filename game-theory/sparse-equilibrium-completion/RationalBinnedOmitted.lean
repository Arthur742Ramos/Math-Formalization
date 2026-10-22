/- AI-assisted formalization under the repository Apache-2.0 license.
The source's omitted rows have exactly zero residual response. -/
module
public import RationalBinnedWeights
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalUniformScore {m : ℕ} (r : ℚ) (j : Fin m) : ℚ :=
  r*((m : ℚ)-((2 : ℕ) : ℚ)*(j.val : ℚ)-1)/(m : ℚ)

theorem rational_binned_label_representative {h : ℕ}
    (L : Fin h → ℕ) (hL : ∀ b,0 < L b) (b : Fin h × Fin 2) :
    rationalBinRepresentative L (rationalBinnedLabel L hL b)=true := by
  simp only [rationalBinRepresentative,decide_eq_true_eq]
  unfold rationalBinDecode rationalBinnedLabel binnedLabel binIndex
  rw [Equiv.symm_apply_apply]
  by_cases hb : b.2.val=0
  all_goals simp [binCompressedLabel,binLower,binUpper,hb]

theorem rational_binned_nonrepresentative_zero {h : ℕ}
    (L : Fin h → ℕ) (hL : ∀ b,0 < L b) (r : ℚ) (j : Fin (∑ b,L b))
    (hj : rationalBinRepresentative L j=false) : rationalBinnedWeights L hL r j=0 := by
  apply Finset.sum_eq_zero
  intro b _
  have hne : rationalBinnedLabel L hL b ≠ j := by
    intro he
    have hh := rational_binned_label_representative L hL b
    rw [he,hj] at hh
    cases hh
  simp only [hne,ite_false]

theorem rational_binned_omitted_response {h : ℕ}
    (L : Fin h → ℕ) (hL : ∀ b,0 < L b) (r : ℚ) (hm : 0 < ∑ b,L b)
    (i : Fin (∑ b,L b)) (hi : rationalBinRepresentative L i=false) :
    rationalUniformScore r i+
      (∑ j,rationalExplicitBinPayoff L i j*rationalBinnedWeights L hL r j)=0 := by
  have he : (∑ j,rationalExplicitBinPayoff L i j*rationalBinnedWeights L hL r j)=
      rationalOmittedCoefficient i*(∑ j,rationalBinnedWeights L hL r j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    cases hj : rationalBinRepresentative L j
    · rw [rational_binned_nonrepresentative_zero L hL r j hj,mul_zero,mul_zero]
    · simp only [rationalExplicitBinPayoff,hi,hj,Bool.false_eq_true,ite_false,ite_true]
  rw [he,rational_binned_weights_mass L hL r hm]
  unfold rationalUniformScore rationalOmittedCoefficient
  ring

end SparseCompletion
