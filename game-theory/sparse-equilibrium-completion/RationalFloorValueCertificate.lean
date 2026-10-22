/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import RationalFloorClassWitness
public import RationalInitializedUpperWitness
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem rational_floor_grid_value_certificate {k m : ℕ} [Nonempty (Fin k ⊕ Fin m)]
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ) (u : Fin m → ℚ)
    (hs : ∀ a,0 ≤ s a) (hu : ∀ i,0 ≤ u i) (hR : d.R=rationalResidualFloors u)
    (hne : (floorIntervalGameClass d s u).Nonempty)
    (δ : ℚ) (hδ : 0 < δ) (j : Fin m) (ζ : ℚ) (hζ : 0 < ζ) :
    ∃ w : (Fin k → ℚ) × RationalIntervalRationalOutput k m,
      rationalAllocationSearch d s hs δ ζ=some w ∧
      floorIntervalGameValue d s u ≤ (w.2.bracket.2 : ℝ)+(d.η : ℝ) ∧
      (w.2.bracket.2 : ℝ)+(d.η : ℝ) < floorIntervalGameValue d s u+
        (2 : ℕ)*(d.M : ℝ)*k*(δ : ℝ)+(ζ : ℝ)+(d.η : ℝ) := by
  obtain ⟨⟨p,q,D,K,B⟩,hz0,he⟩ := floor_interval_game_value_attained d s u hne
  rcases hz0 with ⟨⟨_,_,hDI,hKI,hB,hBI⟩,hsp,huq,hmass,hK⟩
  obtain ⟨z,hz,hc,q',hClass,hE⟩ := rational_floor_grid_game d s u hs hu hR p q K D B
    hsp huq hmass hK (fun a b => ⟨hKI.1 a b,hKI.2 a b⟩)
    (fun i a => ⟨hDI.1 i a,hDI.2 i a⟩) hB hBI δ hδ j
  change exploitability (blockMatrix K D B) (blockWeights p q)=floorIntervalGameValue d s u at he
  rw [he] at hE
  let dz := d.withAllocation (rationalAnchorAllocation s δ z)
    (fun a => le_trans (hs a) (hz a))
  obtain ⟨v,hv⟩ := rational_interval_initialized_complete dz ζ hc
  have hRun : rationalAllocationRun d s hs ζ (rationalAnchorAllocation s δ z)=
      some (rationalAnchorAllocation s δ z,v) := by
    simp only [rationalAllocationRun,dite_eq_left hz]
    change (rationalIntervalInitializedApproximation dz ζ).map
      (fun o => (rationalAnchorAllocation s δ z,o))=some (rationalAnchorAllocation s δ z,v)
    rw [hv]
    rfl
  have hSuccess : ∃ w,rationalAllocationSearch d s hs δ ζ=some w := by
    rw [rationalAllocationSearch,rational_finite_select_success_iff]
    exact ⟨z,rational_allocation_nodes_complete k δ z,_,hRun⟩
  obtain ⟨w,hw⟩ := hSuccess
  have hmin := rational_allocation_search_minimal d s hs δ ζ w hw z _ hRun
  have hminR : (w.2.bracket.2 : ℝ) ≤ (v.bracket.2 : ℝ) := by exact_mod_cast hmin
  have hU := rational_initialized_upper_lt_witness dz ζ hζ v hv hc (q',D,K,B) hClass
  change (v.bracket.2 : ℝ) < exploitability (blockMatrix K D B)
    (blockWeights (fun a => (rationalAnchorAllocation s δ z a : ℝ)) q')+(ζ : ℝ) at hU
  have hGlobal := rational_floor_search_output_class d s u hs hR δ ζ w hw
  have hLower := floor_interval_game_value_le_witness d s u _ hGlobal
  obtain ⟨zw,hzw⟩ := rational_allocation_search_output d s hs δ ζ w hw
  obtain ⟨_,_,_,hrows⟩ := rational_allocation_run_game d s hs ζ _ w hzw
  have hUpper : floorIntervalGameExploitability ((fun a => (w.1 a : ℝ)),w.2.realData) ≤
      (w.2.bracket.2 : ℝ)+(d.η : ℝ) := by
    exact (exploitability_le_iff _ _ _).mpr hrows
  exact ⟨w,hw,le_trans hLower hUpper,by linarith⟩

end
end SparseCompletion
