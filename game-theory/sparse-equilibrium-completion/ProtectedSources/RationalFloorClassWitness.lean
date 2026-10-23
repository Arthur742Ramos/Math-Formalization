/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.RationalFloorClass
public import ProtectedSources.RationalAllocationSearchSoundness
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem floor_interval_game_class_of_fixed {k m : ℕ}
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ) (u : Fin m → ℚ)
    (hs : ∀ a,0 ≤ s a) (hR : d.R=rationalResidualFloors u)
    (p : Fin k → ℚ) (hsp : ∀ a,s a ≤ p a)
    (hc : (d.withAllocation p (fun a => le_trans (hs a) (hsp a))).Compatible)
    (z : IntervalGameData k m)
    (hz : z ∈ intervalGameClass ((d.withAllocation p (fun a => le_trans (hs a) (hsp a))).toModel hc)) :
    ((fun a => (p a : ℝ)),z) ∈ floorIntervalGameClass d s u := by
  rcases hz with ⟨⟨⟨hq,_⟩,hD,hK,hB,hBI⟩,hm,hKs,hRp⟩
  have hp0 : ∀ a,0 ≤ (p a : ℝ) := fun a => by exact_mod_cast le_trans (hs a) (hsp a)
  have hmass : (∑ a,(p a : ℝ))+(∑ i,z.1 i)=1 := by
    change (∑ i,z.1 i)=((1-∑ a,p a : ℚ) : ℝ) at hm
    push_cast at hm
    linarith
  have hp1 : ∀ a,(p a : ℝ) ≤ 1 := by
    intro a
    have hsingle := Finset.single_le_sum (fun b _ => hp0 b) (Finset.mem_univ a)
    have hqsum : 0 ≤ ∑ i,z.1 i := Finset.sum_nonneg fun i _ => hq i
    linarith
  have hq1 : ∀ i,z.1 i ≤ 1 := by
    intro i
    have hsingle := Finset.single_le_sum (fun l _ => hq l) (Finset.mem_univ i)
    have hpsum : 0 ≤ ∑ a,(p a : ℝ) := Finset.sum_nonneg fun a _ => hp0 a
    linarith
  refine ⟨⟨⟨hp0,hp1⟩,⟨hq,hq1⟩,hD,hK,hB,hBI⟩,
    (fun a => by change (s a : ℝ) ≤ (p a : ℝ); exact_mod_cast hsp a),?_,hmass,hKs⟩
  change d.R.RealSatisfies
    (intervalPack z.1 (fun i a => z.1 i*z.2.1 i a) z.2.2.1 (H := 0) Fin.elim0) at hRp
  rw [hR,rational_residual_floors_real_pack] at hRp
  exact hRp

theorem floor_interval_game_value_le_witness {k m : ℕ} {I : Type*} [Nonempty (Fin k ⊕ Fin m)]
    (d : RationalIntervalParameters k m I) (s : Fin k → ℚ) (u : Fin m → ℚ)
    (z : FloorIntervalGameData k m) (hz : z ∈ floorIntervalGameClass d s u) :
    floorIntervalGameValue d s u ≤ floorIntervalGameExploitability z := by
  apply csInf_le ((floor_interval_game_class_compact d s u).image
    floor_interval_game_exploitability_continuous).bddBelow
  exact ⟨z,hz,rfl⟩

theorem rational_floor_search_output_class {k m : ℕ}
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ) (u : Fin m → ℚ)
    (hs : ∀ a,0 ≤ s a) (hR : d.R=rationalResidualFloors u) (δ ζ : ℚ)
    (w : (Fin k → ℚ) × RationalIntervalRationalOutput k m)
    (hout : rationalAllocationSearch d s hs δ ζ=some w) :
    ((fun a => (w.1 a : ℝ)),w.2.realData) ∈ floorIntervalGameClass d s u := by
  obtain ⟨z,hz⟩ := rational_allocation_search_output d s hs δ ζ w hout
  obtain ⟨hsp,hc,hClass,_⟩ := rational_allocation_run_game d s hs ζ _ w hz
  exact floor_interval_game_class_of_fixed d s u hs hR w.1 hsp hc w.2.realData hClass

end
end SparseCompletion
