/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.RationalIntervalInitializedSoundness
@[expose] public section
namespace SparseCompletion
noncomputable section

theorem rational_initialized_upper_lt_witness {k m : ℕ} {I : Type*} [Fintype I]
    [Nonempty (Fin k ⊕ Fin m)] (d : RationalIntervalParameters k m I)
    (ζ : ℚ) (hζ : 0 < ζ) (o : RationalIntervalRationalOutput k m)
    (hout : rationalIntervalInitializedApproximation d ζ=some o)
    (hc : d.Compatible) (z : IntervalGameData k m) (hz : z ∈ intervalGameClass (d.toModel hc)) :
    (o.bracket.2 : ℝ) < intervalGameExploitability (d.toModel hc) z+(ζ : ℝ) := by
  obtain ⟨hc',hL,_,hwidth⟩ := rational_interval_initialized_value d ζ hζ o hout
  have hv := interval_game_value_le_witness (d.toModel hc) z hz
  have he : d.toModel hc'=d.toModel hc := rfl
  rw [he] at hL
  linarith

end
end SparseCompletion
