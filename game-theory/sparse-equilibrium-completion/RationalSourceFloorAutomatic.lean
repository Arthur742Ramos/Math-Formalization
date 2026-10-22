/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import RationalSourceFloorParameters
@[expose] public section
namespace SparseCompletion
noncomputable section

theorem rational_source_floor_approximation_global {k m : ℕ} [Nonempty (Fin k ⊕ Fin m)]
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ) (u : Fin m → ℚ)
    (hs : ∀ a,0 ≤ s a) (hu : ∀ i,0 ≤ u i) (hR : d.R=rationalResidualFloors u)
    (hne : (floorIntervalGameClass d s u).Nonempty) (ε : ℚ) (hε : 0 < ε) :
    ∃ w : (Fin k → ℚ) × RationalIntervalRationalOutput k m,
      rationalSourceFloorApproximation d s hs ε=some w ∧
      floorIntervalGameValue d s u ≤ (w.2.bracket.2 : ℝ)+(ε : ℝ)/((3 : ℕ) : ℝ) ∧
      (w.2.bracket.2 : ℝ)+(ε : ℝ)/((3 : ℕ) : ℝ) < floorIntervalGameValue d s u+(ε : ℝ) := by
  let de := d.withSlack (ε/((3 : ℕ) : ℚ)) (rational_third_positive ε hε)
  obtain ⟨w,hw,hlo,hhi⟩ := rational_floor_search_value_certificate de s u hs hu hR hne
    (rationalSourceFloorAllocationStep d.M ε k)
    (rational_source_floor_step_positive d.M ε k d.positiveBound hε)
    (ε/((3 : ℕ) : ℚ)) (rational_third_positive ε hε)
  change floorIntervalGameValue d s u ≤ (w.2.bracket.2 : ℝ)+((ε/((3 : ℕ) : ℚ) : ℚ) : ℝ) at hlo
  change (w.2.bracket.2 : ℝ)+((ε/((3 : ℕ) : ℚ) : ℚ) : ℝ) < floorIntervalGameValue d s u+
    (2 : ℕ)*(d.M : ℝ)*k*(rationalSourceFloorAllocationStep d.M ε k : ℝ)+
      ((ε/((3 : ℕ) : ℚ) : ℚ) : ℝ)+((ε/((3 : ℕ) : ℚ) : ℚ) : ℝ) at hhi
  push_cast at hlo hhi
  have hBudget : (2 : ℕ)*(d.M : ℝ)*k*(rationalSourceFloorAllocationStep d.M ε k : ℝ)+
      (ε : ℝ)/((3 : ℕ) : ℝ)+(ε : ℝ)/((3 : ℕ) : ℝ) ≤ (ε : ℝ) := by
    exact_mod_cast rational_source_floor_error_budget d.M ε k d.positiveBound hε
  refine ⟨w,?_,hlo,?_⟩
  · simp only [rationalSourceFloorApproximation,dite_eq_left hε]
    exact hw
  · linarith

end
end SparseCompletion
