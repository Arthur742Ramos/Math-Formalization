/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import RationalIntervalInitialize
@[expose] public section
namespace SparseCompletion

structure RationalIntervalRationalOutput (k m : ℕ) where
  bracket : ℚ × ℚ
  q : Fin m → ℚ
  K : Fin k → Fin k → ℚ
  D : Fin m → Fin k → ℚ
  B : Fin m → Fin m → ℚ

def rationalIntervalPackOutput {k m : ℕ} {I : Type*} (d : RationalIntervalModel k m I)
    (w : (ℚ × ℚ) × ((Fin (m+(m*k+(k*k+rationalGridSize d.M d.r d.η*m))) → ℚ) ×
      (Fin m → Fin m → ℚ))) : RationalIntervalRationalOutput k m where
  bracket := w.1
  q := intervalQ w.2.1
  K := intervalK w.2.1
  D := rationalIntervalRecover d.lo (intervalV w.2.1) (intervalQ w.2.1)
  B := w.2.2

def rationalIntervalInitializedApproximation {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) (ζ : ℚ) : Option (RationalIntervalRationalOutput k m) :=
  (rationalIntervalInitialize d).bind (fun model =>
    (rationalIntervalAccurateApproximation model ζ).map (rationalIntervalPackOutput model))

theorem rational_interval_initialized_output {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) (ζ : ℚ) (o : RationalIntervalRationalOutput k m)
    (hout : rationalIntervalInitializedApproximation d ζ=some o) :
    ∃ model, rationalIntervalInitialize d=some model ∧
      ∃ z x B, rationalIntervalAccurateApproximation model ζ=some (z,(x,B)) ∧
        o=rationalIntervalPackOutput model (z,(x,B)) := by
  cases hm : rationalIntervalInitialize d with
  | none => simp only [rationalIntervalInitializedApproximation,hm,Option.bind_none] at hout; cases hout
  | some model =>
    cases ha : rationalIntervalAccurateApproximation model ζ with
    | none => simp only [rationalIntervalInitializedApproximation,hm,Option.bind_some,ha,Option.map_none] at hout; cases hout
    | some w =>
      have he : rationalIntervalPackOutput model w=o := Option.some.inj
        (by simpa only [rationalIntervalInitializedApproximation,hm,Option.bind_some,ha,Option.map_some] using hout)
      exact ⟨model,rfl,w.1,w.2.1,w.2.2,ha,he.symm⟩

theorem rational_interval_initialized_complete {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) (ζ : ℚ) (hc : d.Compatible) :
    ∃ o, rationalIntervalInitializedApproximation d ζ=some o := by
  obtain ⟨z,x,B,hout⟩ := rational_interval_accurate_complete (d.toModel hc) ζ
  exact ⟨rationalIntervalPackOutput (d.toModel hc) (z,(x,B)),by
    simp only [rationalIntervalInitializedApproximation,rational_interval_initialize_complete d hc,
      Option.bind_some,hout,Option.map_some]⟩

theorem rational_interval_initialized_none_iff {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) (ζ : ℚ) :
    rationalIntervalInitializedApproximation d ζ=none ↔ ¬d.Compatible := by
  constructor
  · intro hn hc
    obtain ⟨o,ho⟩ := rational_interval_initialized_complete d ζ hc
    rw [hn] at ho
    cases ho
  · intro hn
    have hi := (rational_interval_initialize_none_iff d).mpr hn
    simp only [rationalIntervalInitializedApproximation,hi,Option.bind_none]

end SparseCompletion
