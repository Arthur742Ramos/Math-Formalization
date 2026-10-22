/- AI-assisted formalization under the repository Apache-2.0 license.
The source-explicit residual matrix is retained through core-only uncertainty. -/
module
public import ExplicitBinnedGame
public import CoreAdjustment
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

def explicitBinnedError {h : ℕ} (L : Fin h → ℕ) : ℝ :=
  (1/(4 : ℕ) : ℝ)^(2 : ℕ)/((12 : ℕ)*((∑ b,L b : ℕ) : ℝ)^(3 : ℕ))*
    ∑ b,binParityTerm (L b)

theorem explicit_binned_core_witness {h : ℕ} (L : Fin h → ℕ) (hL : ∀ b,0 < L b)
    (hm : 0 < ∑ b,L b) (ε δ : ℝ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (heff : explicitBinnedError L ≤ ε+(((3 : ℕ) : ℝ)/(8 : ℕ))*δ) :
    ∃ u, UniformCoreWitness (∑ b,L b) ε δ
      (binnedWeights L hL (1/(4 : ℕ))) u (explicitBinnedMatrix L) := by
  obtain ⟨d,hq,hmass,hB,hb,_,hd,hβ,_,h0,h1,hrows,he⟩ := explicit_binned_game_witness L hL hm
  apply uniform_core_adjust hm (binnedWeights L hL (1/(4 : ℕ))) (explicitBinnedMatrix L)
    d ε δ hq hmass hB hb hd hβ hε hδ
  · rw [he]
    exact heff
  · exact h0
  · exact h1
  · intro j
    exact le_of_eq (hrows j)

end
end SparseCompletion
