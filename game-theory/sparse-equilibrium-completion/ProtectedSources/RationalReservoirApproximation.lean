/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.RationalAllocationGrid
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem rational_reservoir_grid_approximation {k : ℕ} [Nonempty (Fin k)]
    (s : Fin k → ℚ) (p : Fin k → ℝ) (δ M : ℚ) (j : Fin k)
    (A : Fin k → Fin k → ℝ) (hs : ∀ i,0 ≤ s i)
    (hp : p ∈ floorStrategies (fun i => (s i : ℝ))) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hA : ∀ i l,|A i l| ≤ (M : ℝ)) :
    ∃ z : Fin k → Fin (1+Nat.floor (1/δ)),
      (fun i => (rationalReservoirAllocation s δ j z i : ℝ)) ∈
        floorStrategies (fun i => (s i : ℝ)) ∧
      exploitability A (fun i => (rationalReservoirAllocation s δ j z i : ℝ)) ≤
        exploitability A p+(2 : ℕ)*(M : ℝ)*k*(δ : ℝ) := by
  have hfloor : Nat.floor (1/(δ : ℝ))=Nat.floor (1/δ) := by
    rw [show 1/(δ : ℝ)=((1/δ : ℚ) : ℝ) by push_cast; rfl,rational_nat_floor_real_cast]
  obtain ⟨z,hz,hv⟩ := reservoir_grid_approximation (fun i => (s i : ℝ)) p
    (δ : ℝ) (M : ℝ) j A (fun i => by exact_mod_cast hs i) hp
    (by exact_mod_cast hδ) (by exact_mod_cast hM) hA
  let zQ : Fin k → Fin (1+Nat.floor (1/δ)) :=
    fun i => ⟨(z i).val,by rw [←hfloor]; exact (z i).isLt⟩
  have he : (fun i => (rationalReservoirAllocation s δ j zQ i : ℝ))=
      reservoirGridAllocation (fun i => (s i : ℝ)) (δ : ℝ) j z := by
    rw [rational_reservoir_allocation_real]
    congr 1
  refine ⟨zQ,he.symm ▸ hz,?_⟩
  rw [he]
  simpa only [Fintype.card_fin] using hv

end
end SparseCompletion
