/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.RationalFloorClassWitness
@[expose] public section
namespace SparseCompletion
noncomputable section

theorem rational_floor_reservoir_output_class {k m : ℕ}
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ) (u : Fin m → ℚ)
    (hs : ∀ a,0 ≤ s a) (hR : d.R=rationalResidualFloors u) (δ ζ : ℚ) (j : Fin k)
    (w : (Fin k → ℚ) × RationalIntervalRationalOutput k m)
    (hout : rationalReservoirSearch d s hs δ ζ j=some w) :
    ((fun a => (w.1 a : ℝ)),w.2.realData) ∈ floorIntervalGameClass d s u := by
  obtain ⟨z,hz⟩ := rational_reservoir_search_output d s hs δ ζ j w hout
  obtain ⟨hsp,hc,hClass,_⟩ := rational_allocation_run_game d s hs ζ _ w hz
  exact floor_interval_game_class_of_fixed d s u hs hR w.1 hsp hc w.2.realData hClass

end
end SparseCompletion
