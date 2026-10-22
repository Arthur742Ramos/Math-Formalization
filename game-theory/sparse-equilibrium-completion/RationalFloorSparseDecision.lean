/- AI-assisted formalization under the repository Apache-2.0 license. -/
module
public import RationalFloorSparseSupport
@[expose] public section
namespace SparseCompletion

def rationalSparseFloorClassDecision {k m : ℕ}
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (hR : d.R=rationalResidualFloors (fun _ => 0)) (ε : ℚ) (hε : 0 < ε) :
    Decidable (floorIntervalGameClass d s (fun _ => 0)).Nonempty :=
  (Option.rec (motive := fun o => rationalFloorSparseApproximation d s hs ε=o →
      Decidable (floorIntervalGameClass d s (fun _ => 0)).Nonempty)
    (fun he => isFalse ((rational_floor_sparse_none_iff d s hs hR ε hε).mp he))
    (fun v he => isTrue ⟨_,(rational_floor_sparse_output_game d s hs hR ε v he).1⟩)
    (rationalFloorSparseApproximation d s hs ε)) rfl

theorem rational_floor_sparse_nonpositive {k m : ℕ}
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (ε : ℚ) (hε : ε ≤ 0) : rationalFloorSparseApproximation d s hs ε=none := by
  simp only [rationalFloorSparseApproximation,not_lt.mpr hε,ite_false]

theorem rational_floor_sparse_empty (d : RationalIntervalParameters 0 0 (Fin 0))
    (s : Fin 0 → ℚ) (hs : ∀ a,0 ≤ s a) (ε : ℚ) :
    rationalFloorSparseApproximation d s hs ε=none := by
  unfold rationalFloorSparseApproximation
  rw [rational_floor_approximation_empty]
  split_ifs <;> rfl

end SparseCompletion
