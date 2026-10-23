/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed.
Physical consistency is computed by the verified rational program, not arbitrary Real comparison. -/
module
public import ProtectedSources.RationalIntervalConsistency
@[expose] public section
namespace SparseCompletion

theorem rational_interval_algorithm_none_incompatible {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I)
    (h : rationalIntervalRepertoireAlgorithm d.loK d.hiK d.lo d.hi d.p d.M d.r d.M d.η d.R=none) :
    ¬d.Compatible := by
  intro hc
  obtain ⟨x,B,hout⟩ := rational_interval_compatible_success d hc
  rw [h] at hout
  cases hout

instance rationalIntervalCompatibilityDecidable {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) : Decidable d.Compatible :=
  (Option.rec
    (motive := fun o => rationalIntervalRepertoireAlgorithm d.loK d.hiK d.lo d.hi d.p
      d.M d.r d.M d.η d.R=o → Decidable d.Compatible)
    (fun he => isFalse (rational_interval_algorithm_none_incompatible d he))
    (fun w he => isTrue (rational_interval_success_compatible d w.1 w.2 he))
    (rationalIntervalRepertoireAlgorithm d.loK d.hiK d.lo d.hi d.p d.M d.r d.M d.η d.R)) rfl

def rationalIntervalInitialize {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) : Option (RationalIntervalModel k m I) :=
  dite d.Compatible (fun hc => some (d.toModel hc)) (fun _ => none)

theorem rational_interval_initialize_complete {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) (h : d.Compatible) :
    rationalIntervalInitialize d=some (d.toModel h) := by
  simp only [rationalIntervalInitialize,dite_eq_left h]

theorem rational_interval_initialize_sound {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) (model : RationalIntervalModel k m I)
    (h : rationalIntervalInitialize d=some model) :
    ∃ hc : d.Compatible, model=d.toModel hc := by
  by_cases hc : d.Compatible
  · exact ⟨hc,(Option.some.inj (by simpa only [rationalIntervalInitialize,dite_eq_left hc] using h)).symm⟩
  · simp only [rationalIntervalInitialize,dite_eq_right hc] at h
    cases h

theorem rational_interval_initialize_none_iff {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) : rationalIntervalInitialize d=none ↔ ¬d.Compatible := by
  by_cases hc : d.Compatible <;> simp only [rationalIntervalInitialize,hc,dite_eq_left,dite_eq_right,
    Option.some_ne_none,not_true_eq_false,not_false_eq_true]

end SparseCompletion
