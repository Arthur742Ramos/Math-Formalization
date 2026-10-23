/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.RationalFloorAutomatic
public import ProtectedSources.RationalFloorTotalClass
@[expose] public section
namespace SparseCompletion

theorem floor_interval_class_nonempty_actions {k m : ℕ} {I : Type*}
    (d : RationalIntervalParameters k m I) (s : Fin k → ℚ) (u : Fin m → ℚ)
    (hne : (floorIntervalGameClass d s u).Nonempty) : Nonempty (Fin k ⊕ Fin m) := by
  by_cases hk : 0 < k
  · exact ⟨Sum.inl ⟨0,hk⟩⟩
  · by_cases hm : 0 < m
    · exact ⟨Sum.inr ⟨0,hm⟩⟩
    · have hk0 : k=0 := by omega
      have hm0 : m=0 := by omega
      subst k
      subst m
      obtain ⟨z,hz⟩ := hne
      have hmass := hz.2.2.2.1
      norm_num at hmass

theorem rational_floor_approximation_none_iff {k m : ℕ}
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ) (u : Fin m → ℚ)
    (hs : ∀ a,0 ≤ s a) (hu : ∀ i,0 ≤ u i) (hR : d.R=rationalResidualFloors u)
    (ε : ℚ) (hε : 0 < ε) :
    rationalFloorApproximation d s hs ε=none ↔ ¬(floorIntervalGameClass d s u).Nonempty := by
  constructor
  · intro hn hne
    let _ := floor_interval_class_nonempty_actions d s u hne
    obtain ⟨w,hw,_,_⟩ := rational_floor_approximation_global d s u hs hu hR hne ε hε
    rw [hn] at hw
    cases hw
  · intro hn
    cases hr : rationalFloorApproximation d s hs ε with
    | none => rfl
    | some w =>
      exact False.elim (hn ⟨_,rational_floor_approximation_output_class d s u hs hR ε w hr⟩)

theorem rational_floor_approximation_empty (d : RationalIntervalParameters 0 0 (Fin 0))
    (s : Fin 0 → ℚ) (hs : ∀ a,0 ≤ s a) (ε : ℚ) :
    rationalFloorApproximation d s hs ε=none := by
  simp [rationalFloorApproximation,rationalFloorSearch]

def rationalFloorClassDecision {k m : ℕ}
    (d : RationalIntervalParameters k m (Fin m)) (s : Fin k → ℚ) (u : Fin m → ℚ)
    (hs : ∀ a,0 ≤ s a) (hu : ∀ i,0 ≤ u i) (hR : d.R=rationalResidualFloors u)
    (ε : ℚ) (hε : 0 < ε) : Decidable (floorIntervalGameClass d s u).Nonempty :=
  (Option.rec (motive := fun o => rationalFloorApproximation d s hs ε=o →
      Decidable (floorIntervalGameClass d s u).Nonempty)
    (fun he => isFalse ((rational_floor_approximation_none_iff d s u hs hu hR ε hε).mp he))
    (fun w he => isTrue ⟨_,rational_floor_approximation_output_class d s u hs hR ε w he⟩)
    (rationalFloorApproximation d s hs ε)) rfl

end SparseCompletion
