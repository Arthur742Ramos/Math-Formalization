/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import RationalNoResidualAccuracy
public import RationalReservoirClass
public import RationalInitializedUpperWitness
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem rational_no_residual_global_certificate {k : ℕ} [Nonempty (Fin k ⊕ Fin 0)]
    (d : RationalIntervalParameters k 0 (Fin 0)) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (hR : d.R=rationalResidualFloors (Fin.elim0 : Fin 0 → ℚ))
    (hne : (floorIntervalGameClass d s Fin.elim0).Nonempty)
    (δ : ℚ) (hδ : 0 < δ) (j : Fin k) (ζ : ℚ) (hζ : 0 < ζ) :
    ∃ w : (Fin k → ℚ) × RationalIntervalRationalOutput k 0,
      rationalReservoirSearch d s hs δ ζ j=some w ∧
      floorIntervalGameValue d s Fin.elim0 ≤ (w.2.bracket.2 : ℝ)+(d.η : ℝ) ∧
      (w.2.bracket.2 : ℝ)+(d.η : ℝ) < floorIntervalGameValue d s Fin.elim0+
        (2 : ℕ)*(d.M : ℝ)*k*(δ : ℝ)+(ζ : ℝ)+(d.η : ℝ) := by
  obtain ⟨⟨p,q,D,K,B⟩,hz0,he⟩ := floor_interval_game_value_attained d s Fin.elim0 hne
  have hq : q=(Fin.elim0 : Fin 0 → ℝ) := funext fun i => Fin.elim0 i
  have hD : D=(Fin.elim0 : Fin 0 → Fin k → ℝ) := funext fun i => Fin.elim0 i
  have hB : B=(Fin.elim0 : Fin 0 → Fin 0 → ℝ) := funext fun i => Fin.elim0 i
  subst q
  subst D
  subst B
  rcases hz0 with ⟨⟨_,_,_,hKI,_,_⟩,hsp,_,hmass,hK⟩
  have hp : p ∈ floorStrategies (fun a => (s a : ℝ)) :=
    ⟨hsp,by simpa only [Fin.sum_univ_zero,add_zero] using hmass⟩
  obtain ⟨z,hz,hc,hClass,hE⟩ := rational_no_residual_grid_game d s hs hR p hp K hK
    (fun a b => ⟨hKI.1 a b,hKI.2 a b⟩) δ hδ j
  change exploitability (blockMatrix K (Fin.elim0 : Fin 0 → Fin k → ℝ) Fin.elim0)
    (blockWeights p Fin.elim0)=floorIntervalGameValue d s Fin.elim0 at he
  rw [he] at hE
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
  have hminR : (w.2.bracket.2 : ℝ) ≤ (v.bracket.2 : ℝ) := by exact_mod_cast hmin
  have hU := rational_initialized_upper_lt_witness dz ζ hζ v hv hc
    (Fin.elim0,Fin.elim0,K,Fin.elim0) hClass
  change (v.bracket.2 : ℝ) <
    exploitability (blockMatrix K (Fin.elim0 : Fin 0 → Fin k → ℝ) Fin.elim0)
      (blockWeights (fun a => (rationalReservoirAllocation s δ j z a : ℝ)) Fin.elim0)+(ζ : ℝ) at hU
  have hGlobal := rational_floor_reservoir_output_class d s Fin.elim0 hs hR δ ζ j w hw
  have hLower := floor_interval_game_value_le_witness d s Fin.elim0 _ hGlobal
  obtain ⟨zw,hzw⟩ := rational_reservoir_search_output d s hs δ ζ j w hw
  obtain ⟨_,_,_,hrows⟩ := rational_allocation_run_game d s hs ζ _ w hzw
  have hUpper : floorIntervalGameExploitability ((fun a => (w.1 a : ℝ)),w.2.realData) ≤
      (w.2.bracket.2 : ℝ)+(d.η : ℝ) := by
    exact (exploitability_le_iff _ _ _).mpr hrows
  exact ⟨w,hw,le_trans hLower hUpper,by linarith⟩

end
end SparseCompletion
