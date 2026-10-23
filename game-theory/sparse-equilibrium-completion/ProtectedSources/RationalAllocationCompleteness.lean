/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.RationalAllocationRun
@[expose] public section
namespace SparseCompletion

theorem rational_allocation_run_success_iff {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (ζ : ℚ) (p : Fin k → ℚ) :
    (∃ w,rationalAllocationRun d s hs ζ p=some w) ↔
      ∃ h : ∀ a,s a ≤ p a,(d.withAllocation p (fun a => le_trans (hs a) (h a))).Compatible := by
  constructor
  · rintro ⟨w,hw⟩
    obtain ⟨h,ho,_⟩ := rational_allocation_run_output d s hs ζ p w hw
    obtain ⟨hc,_,_⟩ := rational_interval_initialized_game
      (d.withAllocation p (fun a => le_trans (hs a) (h a))) ζ w.2 ho
    exact ⟨h,hc⟩
  · rintro ⟨h,hc⟩
    obtain ⟨o,ho⟩ := rational_interval_initialized_complete
      (d.withAllocation p (fun a => le_trans (hs a) (h a))) ζ hc
    refine ⟨(p,o),?_⟩
    simp only [rationalAllocationRun,dite_eq_left h,ho,Option.map_some]

theorem rational_finite_select_success_iff {α β : Type*} (candidates : List α)
    (run : α → Option β) (score : β → ℚ) :
    (∃ o,rationalFiniteSelect candidates run score=some o) ↔
      ∃ a ∈ candidates, ∃ o,run a=some o := by
  constructor
  · rintro ⟨o,ho⟩
    obtain ⟨a,ha,hr⟩ := rational_finite_select_origin candidates run score o ho
    exact ⟨a,ha,o,hr⟩
  · rintro ⟨a,ha,o,hr⟩
    cases hs : rationalFiniteSelect candidates run score with
    | none =>
      have hn := (rational_finite_select_none_iff candidates run score).mp hs a ha
      rw [hn] at hr
      cases hr
    | some v => exact ⟨v,rfl⟩

theorem rational_allocation_search_success_iff {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (δ ζ : ℚ) :
    (∃ w,rationalAllocationSearch d s hs δ ζ=some w) ↔
      ∃ z : Fin k → Fin (1+Nat.floor (1/δ)),
        ∃ h : ∀ a,s a ≤ rationalAnchorAllocation s δ z a,
          (d.withAllocation (rationalAnchorAllocation s δ z)
            (fun a => le_trans (hs a) (h a))).Compatible := by
  rw [rationalAllocationSearch,rational_finite_select_success_iff]
  constructor
  · rintro ⟨z,_,hz⟩
    exact ⟨z,(rational_allocation_run_success_iff d s hs ζ _).mp hz⟩
  · rintro ⟨z,hz⟩
    exact ⟨z,rational_allocation_nodes_complete k δ z,
      (rational_allocation_run_success_iff d s hs ζ _).mpr hz⟩

end SparseCompletion
