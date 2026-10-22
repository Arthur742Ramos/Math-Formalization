/- AI-assisted formalization under the repository Apache-2.0 license. -/
module
public import RationalSourceFloorClass
public import RationalFloorOutputRows
@[expose] public section
namespace SparseCompletion

theorem rational_source_floor_approximation_rows {k m : ℕ}
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (ε : ℚ) (hε : 0 < ε) (w : (Fin k → ℚ) × RationalIntervalRationalOutput k m)
    (hout : rationalSourceFloorApproximation d s hs ε=some w) :
    (∀ a,s a ≤ w.1 a) ∧
    ∀ a,response (intervalGameMatrix w.2.realData)
      (blockWeights (fun a => (w.1 a : ℝ)) (fun i => (w.2.q i : ℝ))) a ≤
        (w.2.bracket.2 : ℝ)+((ε/((3 : ℕ) : ℚ) : ℚ) : ℝ) := by
  simp only [rationalSourceFloorApproximation,dite_eq_left hε] at hout
  exact rational_floor_search_rows _ s hs _ _ w hout

end SparseCompletion
