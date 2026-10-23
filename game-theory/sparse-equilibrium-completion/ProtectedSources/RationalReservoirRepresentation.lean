/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.RationalAllocationGrid
@[expose] public section
namespace SparseCompletion
noncomputable section

theorem rational_reservoir_rounding_enumerated {k : ℕ} (s : Fin k → ℚ)
    (p : Fin k → ℝ) (δ : ℚ) (j : Fin k) (hs : ∀ i,0 ≤ s i)
    (hp : p ∈ floorStrategies (fun i => (s i : ℝ))) (hδ : 0 < δ) :
    ∃ z : Fin k → Fin (1+Nat.floor (1/δ)),
      (fun i => (rationalReservoirAllocation s δ j z i : ℝ))=
        reservoirRounded (fun i => (s i : ℝ)) p (δ : ℝ) j := by
  have hfloor : Nat.floor (1/(δ : ℝ))=Nat.floor (1/δ) := by
    rw [show 1/(δ : ℝ)=((1/δ : ℚ) : ℝ) by push_cast; rfl,rational_nat_floor_real_cast]
  obtain ⟨z,hz⟩ := reservoir_rounded_finite_grid (fun i => (s i : ℝ)) p (δ : ℝ) j
    (fun i => by exact_mod_cast hs i) hp (by exact_mod_cast hδ)
  let zQ : Fin k → Fin (1+Nat.floor (1/δ)) :=
    fun i => ⟨(z i).val,by rw [←hfloor]; exact (z i).isLt⟩
  refine ⟨zQ,?_⟩
  rw [rational_reservoir_allocation_real,hz]
  congr 1

end
end SparseCompletion
