/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.RationalAllocationGrid
@[expose] public section
namespace SparseCompletion
noncomputable section

theorem rational_anchor_rounding_enumerated {k : ℕ} (s : Fin k → ℚ)
    (p : Fin k → ℝ) (δ : ℚ) (hs : ∀ i,0 ≤ s i) (hp : ∀ i,p i ≤ 1) (hδ : 0 < δ) :
    ∃ z : Fin k → Fin (1+Nat.floor (1/δ)),
      ∀ i,(rationalAnchorAllocation s δ z i : ℝ)=
        roundedAllocation (fun i => (s i : ℝ)) p (δ : ℝ) i := by
  have hfloor : Nat.floor (1/(δ : ℝ))=Nat.floor (1/δ) := by
    rw [show 1/(δ : ℝ)=((1/δ : ℚ) : ℝ) by push_cast; rfl,rational_nat_floor_real_cast]
  obtain ⟨z,hz⟩ := rounded_allocation_finite_grid (fun i => (s i : ℝ)) p (δ : ℝ)
    (fun i => by exact_mod_cast hs i) hp (by exact_mod_cast hδ)
  let zQ : Fin k → Fin (1+Nat.floor (1/δ)) :=
    fun i => ⟨(z i).val,by rw [←hfloor]; exact (z i).isLt⟩
  refine ⟨zQ,?_⟩
  intro i
  simpa only [rationalAnchorAllocation,Rat.cast_add,Rat.cast_mul,Rat.cast_natCast] using (hz i).symm

end
end SparseCompletion
