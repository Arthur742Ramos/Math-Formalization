/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.RationalAllocationGrid
public import ProtectedSources.RationalIntervalInitializedSoundness
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def RationalIntervalParameters.withAllocation {k m : ℕ} {I : Type*}
    (d : RationalIntervalParameters k m I) (p : Fin k → ℚ) (hp : ∀ a, 0 ≤ p a) :
    RationalIntervalParameters k m I :=
  {d with p := p, r := 1-∑ a,p a, anchorNonneg := hp, normalized := by ring}

def rationalAllocationRun {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (ζ : ℚ) (p : Fin k → ℚ) : Option ((Fin k → ℚ) × RationalIntervalRationalOutput k m) :=
  if h : ∀ a, s a ≤ p a then
    (rationalIntervalInitializedApproximation
      (d.withAllocation p (fun a => le_trans (hs a) (h a))) ζ).map (fun o => (p,o))
  else none

theorem rational_allocation_run_output {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (ζ : ℚ) (p : Fin k → ℚ) (w : (Fin k → ℚ) × RationalIntervalRationalOutput k m)
    (hout : rationalAllocationRun d s hs ζ p=some w) :
    ∃ h : ∀ a,s a ≤ p a,
      rationalIntervalInitializedApproximation
        (d.withAllocation p (fun a => le_trans (hs a) (h a))) ζ=some w.2 ∧ w.1=p := by
  by_cases h : ∀ a,s a ≤ p a
  · simp only [rationalAllocationRun,dite_eq_left h] at hout
    cases ho : rationalIntervalInitializedApproximation
      (d.withAllocation p (fun a => le_trans (hs a) (h a))) ζ with
    | none => simp only [ho,Option.map_none] at hout; cases hout
    | some o =>
      rw [ho,Option.map_some] at hout
      have he := Option.some.inj hout
      subst w
      exact ⟨h,ho,rfl⟩
  · simp only [rationalAllocationRun,dite_eq_right h] at hout
    cases hout

def rationalAllocationSearch {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (δ ζ : ℚ) : Option ((Fin k → ℚ) × RationalIntervalRationalOutput k m) :=
  rationalFiniteSelect (rationalAllocationNodes k δ)
    (fun z => rationalAllocationRun d s hs ζ (rationalAnchorAllocation s δ z))
    (fun w => w.2.bracket.2)

def rationalReservoirSearch {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (δ ζ : ℚ) (j : Fin k) : Option ((Fin k → ℚ) × RationalIntervalRationalOutput k m) :=
  rationalFiniteSelect (rationalAllocationNodes k δ)
    (fun z => rationalAllocationRun d s hs ζ (rationalReservoirAllocation s δ j z))
    (fun w => w.2.bracket.2)

theorem rational_allocation_search_output {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (δ ζ : ℚ) (w : (Fin k → ℚ) × RationalIntervalRationalOutput k m)
    (hout : rationalAllocationSearch d s hs δ ζ=some w) :
    ∃ z : Fin k → Fin (1+Nat.floor (1/δ)),
      rationalAllocationRun d s hs ζ (rationalAnchorAllocation s δ z)=some w := by
  obtain ⟨z,_,hz⟩ := rational_finite_select_origin _ _ _ w hout
  exact ⟨z,hz⟩

theorem rational_reservoir_search_output {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) (s : Fin k → ℚ) (hs : ∀ a,0 ≤ s a)
    (δ ζ : ℚ) (j : Fin k) (w : (Fin k → ℚ) × RationalIntervalRationalOutput k m)
    (hout : rationalReservoirSearch d s hs δ ζ j=some w) :
    ∃ z : Fin k → Fin (1+Nat.floor (1/δ)),
      rationalAllocationRun d s hs ζ (rationalReservoirAllocation s δ j z)=some w := by
  obtain ⟨z,_,hz⟩ := rational_finite_select_origin _ _ _ w hout
  exact ⟨z,hz⟩

end SparseCompletion
