/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.RationalFloorAccuracyParameters
@[expose] public section
namespace SparseCompletion
noncomputable section

theorem rational_floor_total_output_class {k m : ℕ}
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ) (u : Fin m → ℚ)
    (hs : ∀ a,0 ≤ s a) (hR : d.R=rationalResidualFloors u) (δ ζ : ℚ)
    (w : (Fin k → ℚ) × RationalIntervalRationalOutput k m)
    (hout : rationalFloorSearch d s hs δ ζ=some w) :
    ((fun a => (w.1 a : ℝ)),w.2.realData) ∈ floorIntervalGameClass d s u := by
  by_cases hm : 0 < m
  · simp only [rationalFloorSearch,hm,ite_true] at hout
    exact rational_floor_search_output_class d s u hs hR δ ζ w hout
  · by_cases hk : 0 < k
    · simp only [rationalFloorSearch,hm,ite_false,dite_eq_left hk] at hout
      exact rational_floor_reservoir_output_class d s u hs hR δ ζ ⟨0,hk⟩ w hout
    · simp only [rationalFloorSearch,hm,ite_false,dite_eq_right hk] at hout
      cases hout

theorem rational_floor_approximation_output_class {k m : ℕ}
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ) (u : Fin m → ℚ)
    (hs : ∀ a,0 ≤ s a) (hR : d.R=rationalResidualFloors u) (ε : ℚ)
    (w : (Fin k → ℚ) × RationalIntervalRationalOutput k m)
    (hout : rationalFloorApproximation d s hs ε=some w) :
    ((fun a => (w.1 a : ℝ)),w.2.realData) ∈ floorIntervalGameClass d s u := by
  by_cases he : 0 < ε
  · simp only [rationalFloorApproximation,dite_eq_left he] at hout
    exact rational_floor_total_output_class
      (d.withSlack (ε/((3 : ℕ) : ℚ)) (rational_third_positive ε he)) s u hs hR
      (rationalFloorAllocationStep d.M ε k) (ε/((3 : ℕ) : ℚ)) w hout
  · simp only [rationalFloorApproximation,dite_eq_right he] at hout
    cases hout

end
end SparseCompletion
