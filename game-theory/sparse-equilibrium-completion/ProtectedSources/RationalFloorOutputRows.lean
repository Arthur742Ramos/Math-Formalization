/- AI-assisted formalization under the repository Apache-2.0 license.
The actual global floor program exposes its fixed-slice all-row certificate. -/
module
public import ProtectedSources.RationalFloorDecision
@[expose] public section
namespace SparseCompletion

theorem rational_floor_search_rows {k m : ℕ}
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (δ ζ : ℚ) (w : (Fin k → ℚ) × RationalIntervalRationalOutput k m)
    (hout : rationalFloorSearch d s hs δ ζ=some w) :
    (∀ a,s a ≤ w.1 a) ∧
    ∀ a,response (intervalGameMatrix w.2.realData)
      (blockWeights (fun a => (w.1 a : ℝ)) (fun i => (w.2.q i : ℝ))) a ≤
        (w.2.bracket.2 : ℝ)+(d.η : ℝ) := by
  have hrun : ∃ p,rationalAllocationRun d s hs ζ p=some w := by
    by_cases hm : 0 < m
    · simp only [rationalFloorSearch,hm,ite_true] at hout
      obtain ⟨z,hz⟩ := rational_allocation_search_output d s hs δ ζ w hout
      exact ⟨_,hz⟩
    · by_cases hk : 0 < k
      · simp only [rationalFloorSearch,hm,ite_false,dite_eq_left hk] at hout
        obtain ⟨z,hz⟩ := rational_reservoir_search_output d s hs δ ζ ⟨0,hk⟩ w hout
        exact ⟨_,hz⟩
      · simp only [rationalFloorSearch,hm,ite_false,dite_eq_right hk] at hout
        cases hout
  obtain ⟨p,hp⟩ := hrun
  obtain ⟨h,_,_,hr⟩ := rational_allocation_run_game d s hs ζ p w hp
  exact ⟨h,hr⟩

theorem rational_floor_approximation_rows {k m : ℕ}
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (ε : ℚ) (hε : 0 < ε) (w : (Fin k → ℚ) × RationalIntervalRationalOutput k m)
    (hout : rationalFloorApproximation d s hs ε=some w) :
    (∀ a,s a ≤ w.1 a) ∧
    ∀ a,response (intervalGameMatrix w.2.realData)
      (blockWeights (fun a => (w.1 a : ℝ)) (fun i => (w.2.q i : ℝ))) a ≤
        (w.2.bracket.2 : ℝ)+((ε/((3 : ℕ) : ℚ) : ℚ) : ℝ) := by
  simp only [rationalFloorApproximation,dite_eq_left hε] at hout
  exact rational_floor_search_rows _ s hs _ _ w hout

end SparseCompletion
