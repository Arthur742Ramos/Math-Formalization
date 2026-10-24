module
public import WeakMixingCore

/-! Literal Thick definition and hitting_thick proof retained from source2fae123025f57f2f74220c01ffea7148fc6e3a11, topology/weak-mixing-minimal-product/WeakMixingMinimal.lean. No new claim of this inherited proof. -/
@[expose] public section
open Set Function
namespace WeakMinimal
def Thick (S : Set ℕ) : Prop := ∀ L N : ℕ, ∃ m, N ≤ m ∧ ∀ j ≤ L, m + j ∈ S

theorem hitting_thick {X : Type*} [TopologicalSpace X] [Nonempty X]
    (f : X → X) (hf : Continuous f) (hs : Surjective f) (hw : Furstenberg.WeakMixing f)
    (U V : Set X) (hU : IsOpen U) (hnU : U.Nonempty) (hV : IsOpen V)
    (hnV : V.Nonempty) : Thick {n | Furstenberg.Hit f U V n} := by
  intro L N
  obtain ⟨m, hm⟩ := Furstenberg.finite_simultaneous_hitting f hf hw
    (Finset.range (N + L + 1)) (fun _ => U) (fun j => f^[j] ⁻¹' V)
    (fun _ _ => ⟨hU, hnU⟩) (fun j _ =>
      ⟨hV.preimage (hf.iterate j), hnV.preimage (hs.iterate j)⟩)
  refine ⟨m + N, by omega, ?_⟩
  intro j hj
  obtain ⟨x, hx, hfx⟩ := hm (N + j) (Finset.mem_range.mpr (by omega))
  refine ⟨x, hx, ?_⟩
  simpa only [mem_preimage, ← iterate_add_apply, Nat.add_assoc, Nat.add_comm (N+j) m,
    ← Nat.add_assoc] using hfx
end WeakMinimal
