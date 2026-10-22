/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import RationalAllocationRun
@[expose] public section
namespace SparseCompletion
noncomputable section

theorem rational_allocation_run_game {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (ζ : ℚ) (p : Fin k → ℚ) (w : (Fin k → ℚ) × RationalIntervalRationalOutput k m)
    (hout : rationalAllocationRun d s hs ζ p=some w) :
    ∃ h : ∀ a,s a ≤ w.1 a,
      ∃ hc : (d.withAllocation w.1 (fun a => le_trans (hs a) (h a))).Compatible,
        w.2.realData ∈ intervalGameClass
          ((d.withAllocation w.1 (fun a => le_trans (hs a) (h a))).toModel hc) ∧
        ∀ a, response (intervalGameMatrix w.2.realData)
          (intervalGameWeights ((d.withAllocation w.1
            (fun a => le_trans (hs a) (h a))).toModel hc) w.2.realData) a ≤
              (w.2.bracket.2 : ℝ)+(d.η : ℝ) := by
  obtain ⟨h,ho,hp⟩ := rational_allocation_run_output d s hs ζ p w hout
  rw [hp]
  obtain ⟨hc,hg,hr⟩ := rational_interval_initialized_game
    (d.withAllocation p (fun a => le_trans (hs a) (h a))) ζ w.2 ho
  exact ⟨h,hc,hg,hr⟩

theorem rational_allocation_search_minimal {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (δ ζ : ℚ) (w : (Fin k → ℚ) × RationalIntervalRationalOutput k m)
    (hout : rationalAllocationSearch d s hs δ ζ=some w)
    (z : Fin k → Fin (1+Nat.floor (1/δ)))
    (v : (Fin k → ℚ) × RationalIntervalRationalOutput k m)
    (hv : rationalAllocationRun d s hs ζ (rationalAnchorAllocation s δ z)=some v) :
    w.2.bracket.2 ≤ v.2.bracket.2 :=
  rational_finite_select_minimal _ _ _ w hout z
    (rational_allocation_nodes_complete k δ z) v hv

theorem rational_reservoir_search_minimal {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (δ ζ : ℚ) (j : Fin k) (w : (Fin k → ℚ) × RationalIntervalRationalOutput k m)
    (hout : rationalReservoirSearch d s hs δ ζ j=some w)
    (z : Fin k → Fin (1+Nat.floor (1/δ)))
    (v : (Fin k → ℚ) × RationalIntervalRationalOutput k m)
    (hv : rationalAllocationRun d s hs ζ (rationalReservoirAllocation s δ j z)=some v) :
    w.2.bracket.2 ≤ v.2.bracket.2 :=
  rational_finite_select_minimal _ _ _ w hout z
    (rational_allocation_nodes_complete k δ z) v hv

end
end SparseCompletion
