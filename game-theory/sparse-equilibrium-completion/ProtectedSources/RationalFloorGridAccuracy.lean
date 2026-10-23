/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.RationalFloorGridGame
public import ProtectedSources.RationalAllocationSearchSoundness
@[expose] public section
open scoped BigOperators
namespace SparseCompletion
noncomputable section

theorem rational_floor_grid_search_accuracy {k m : ℕ} [Nonempty (Fin k ⊕ Fin m)]
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ)
    (u : Fin m → ℚ) (hs : ∀ a,0 ≤ s a) (hu : ∀ i,0 ≤ u i)
    (hR : d.R=rationalResidualFloors u)
    (p : Fin k → ℝ) (q : Fin m → ℝ) (K : Fin k → Fin k → ℝ)
    (D : Fin m → Fin k → ℝ) (B : Fin m → Fin m → ℝ)
    (hsp : ∀ a,(s a : ℝ) ≤ p a) (huq : ∀ i,(u i : ℝ) ≤ q i)
    (hmass : (∑ a,p a)+(∑ i,q i)=1) (hK : IsSkew K)
    (hKI : ∀ a b,(d.loK a b : ℝ) ≤ K a b ∧ K a b ≤ (d.hiK a b : ℝ))
    (hDI : ∀ i a,(d.lo i a : ℝ) ≤ D i a ∧ D i a ≤ (d.hi i a : ℝ))
    (hB : IsSkew B) (hBI : ∀ i l,-(d.M : ℝ) ≤ B i l ∧ B i l ≤ (d.M : ℝ))
    (δ : ℚ) (hδ : 0 < δ) (j : Fin m) (ζ : ℚ) (hζ : 0 < ζ) :
    ∃ w : (Fin k → ℚ) × RationalIntervalRationalOutput k m,
      rationalAllocationSearch d s hs δ ζ=some w ∧
      ∀ a, response (intervalGameMatrix w.2.realData)
        (blockWeights (fun b => (w.1 b : ℝ)) (fun i => (w.2.q i : ℝ))) a <
          exploitability (blockMatrix K D B) (blockWeights p q)+
            (2 : ℕ)*(d.M : ℝ)*k*(δ : ℝ)+(ζ : ℝ)+(d.η : ℝ) := by
  obtain ⟨z,hz,hc,q',hClass,hE⟩ := rational_floor_grid_game d s u hs hu hR
    p q K D B hsp huq hmass hK hKI hDI hB hBI δ hδ j
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
  obtain ⟨hc',hL,_,hwidth⟩ := rational_interval_initialized_value dz ζ hζ v hv
  have hVal := interval_game_value_le_witness (dz.toModel hc') (q',D,K,B) hClass
  change intervalGameValue (dz.toModel hc') ≤
    exploitability (blockMatrix K D B)
      (blockWeights (fun a => (rationalAnchorAllocation s δ z a : ℝ)) q') at hVal
  have hminR : (w.2.bracket.2 : ℝ) ≤ (v.bracket.2 : ℝ) := by exact_mod_cast hmin
  obtain ⟨zw,hzw⟩ := rational_allocation_search_output d s hs δ ζ w hw
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
