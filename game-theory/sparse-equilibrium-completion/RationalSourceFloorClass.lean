/- AI-assisted formalization under the repository Apache-2.0 license. -/
module
public import RationalSourceFloorAutomatic
public import RationalFloorTotalClass
public import RationalFloorDecision
@[expose] public section
namespace SparseCompletion
noncomputable section

theorem rational_source_floor_approximation_output_class {k m : ℕ}
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ) (u : Fin m → ℚ)
    (hs : ∀ a,0 ≤ s a) (hR : d.R=rationalResidualFloors u) (ε : ℚ)
    (w : (Fin k → ℚ) × RationalIntervalRationalOutput k m)
    (hout : rationalSourceFloorApproximation d s hs ε=some w) :
    ((fun a => (w.1 a : ℝ)),w.2.realData) ∈ floorIntervalGameClass d s u := by
  by_cases he : 0 < ε
  · simp only [rationalSourceFloorApproximation,dite_eq_left he] at hout
    exact rational_floor_total_output_class
      (d.withSlack (ε/((3 : ℕ) : ℚ)) (rational_third_positive ε he)) s u hs hR
      (rationalSourceFloorAllocationStep d.M ε k) (ε/((3 : ℕ) : ℚ)) w hout
  · simp only [rationalSourceFloorApproximation,dite_eq_right he] at hout
    cases hout


theorem rational_source_floor_none_iff {k m : ℕ}
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ) (u : Fin m → ℚ)
    (hs : ∀ a,0 ≤ s a) (hu : ∀ i,0 ≤ u i) (hR : d.R=rationalResidualFloors u)
    (ε : ℚ) (hε : 0 < ε) :
    rationalSourceFloorApproximation d s hs ε=none ↔
      ¬(floorIntervalGameClass d s u).Nonempty := by
  constructor
  · intro hn hne
    let _ := floor_interval_class_nonempty_actions d s u hne
    obtain ⟨w,hw,_,_⟩ := rational_source_floor_approximation_global d s u hs hu hR hne ε hε
    rw [hn] at hw
    cases hw
  · intro hi
    cases hw : rationalSourceFloorApproximation d s hs ε with
    | none => rfl
    | some w =>
      exact False.elim (hi ⟨_,rational_source_floor_approximation_output_class d s u hs hR ε w hw⟩)


end
end SparseCompletion
