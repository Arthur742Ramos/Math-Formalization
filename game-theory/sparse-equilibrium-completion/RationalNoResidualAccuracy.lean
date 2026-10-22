/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import RationalNoResidualGame
public import RationalAllocationSearchSoundness
public import RationalAllocationCompleteness
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem rational_no_residual_search_accuracy {k : ℕ} [Nonempty (Fin k ⊕ Fin 0)]
    (d : RationalIntervalParameters k 0 (Fin 0)) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (hR : d.R=rationalResidualFloors (Fin.elim0 : Fin 0 → ℚ))
    (p : Fin k → ℝ) (hp : p ∈ floorStrategies (fun a => (s a : ℝ)))
    (K : Fin k → Fin k → ℝ) (hK : IsSkew K)
    (hKI : ∀ a b,(d.loK a b : ℝ) ≤ K a b ∧ K a b ≤ (d.hiK a b : ℝ))
    (δ : ℚ) (hδ : 0 < δ) (j : Fin k) (ζ : ℚ) (hζ : 0 < ζ) :
    ∃ w : (Fin k → ℚ) × RationalIntervalRationalOutput k 0,
      rationalReservoirSearch d s hs δ ζ j=some w ∧
      ∀ a, response (intervalGameMatrix w.2.realData)
        (blockWeights (fun b => (w.1 b : ℝ)) (fun i => (w.2.q i : ℝ))) a <
          exploitability (blockMatrix K (Fin.elim0 : Fin 0 → Fin k → ℝ) Fin.elim0)
            (blockWeights p Fin.elim0)+
            (2 : ℕ)*(d.M : ℝ)*k*(δ : ℝ)+(ζ : ℝ)+(d.η : ℝ) := by
  obtain ⟨z,hz,hc,hClass,hE⟩ := rational_no_residual_grid_game d s hs hR p hp K hK hKI δ hδ j
  let dz := d.withAllocation (rationalReservoirAllocation s δ j z)
    (fun a => le_trans (hs a) (hz a))
  obtain ⟨v,hv⟩ := rational_interval_initialized_complete dz ζ hc
  have hRun : rationalAllocationRun d s hs ζ (rationalReservoirAllocation s δ j z)=
      some (rationalReservoirAllocation s δ j z,v) := by
    simp only [rationalAllocationRun,dite_eq_left hz]
    change (rationalIntervalInitializedApproximation dz ζ).map
      (fun o => (rationalReservoirAllocation s δ j z,o))=some (rationalReservoirAllocation s δ j z,v)
    rw [hv]
    rfl
  have hSuccess : ∃ w,rationalReservoirSearch d s hs δ ζ j=some w := by
    rw [rationalReservoirSearch,rational_finite_select_success_iff]
    exact ⟨z,rational_allocation_nodes_complete k δ z,_,hRun⟩
  obtain ⟨w,hw⟩ := hSuccess
  have hmin := rational_reservoir_search_minimal d s hs δ ζ j w hw z _ hRun
  obtain ⟨hc',hL,_,hwidth⟩ := rational_interval_initialized_value dz ζ hζ v hv
  have hVal := interval_game_value_le_witness (dz.toModel hc')
    (Fin.elim0,Fin.elim0,K,Fin.elim0) hClass
  change intervalGameValue (dz.toModel hc') ≤
    exploitability (blockMatrix K (Fin.elim0 : Fin 0 → Fin k → ℝ) Fin.elim0)
      (blockWeights (fun a => (rationalReservoirAllocation s δ j z a : ℝ)) Fin.elim0) at hVal
  have hminR : (w.2.bracket.2 : ℝ) ≤ (v.bracket.2 : ℝ) := by exact_mod_cast hmin
  obtain ⟨zw,hzw⟩ := rational_reservoir_search_output d s hs δ ζ j w hw
  obtain ⟨_,_,_,hrows⟩ := rational_allocation_run_game d s hs ζ _ w hzw
  refine ⟨w,hw,?_⟩
  intro a
  have hr := hrows a
  change response (intervalGameMatrix w.2.realData)
    (blockWeights (fun b => (w.1 b : ℝ)) (fun i => (w.2.q i : ℝ))) a ≤
      (w.2.bracket.2 : ℝ)+(d.η : ℝ) at hr
  linarith

end
end SparseCompletion
