/- AI-assisted formalization under the repository Apache-2.0 license.
Physical compatibility and sparse value search form one actual rational program. -/
module
public import RationalIntervalSparseApproximation
public import RationalIntervalInitializedSoundness
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def rationalSparseIntervalPackOutput {k m : ℕ}
    (w : (ℚ × ℚ) × RationalSparseIntervalData k m) : RationalIntervalRationalOutput k m where
  bracket := w.1
  q := w.2.1
  K := w.2.2.1
  D := w.2.2.2.1
  B := w.2.2.2.2

def rationalIntervalSparseInitialized {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) (ζ : ℚ) : Option (RationalIntervalRationalOutput k m) :=
  (rationalIntervalInitialize d).bind (fun model =>
    (rationalIntervalSparseAccurate model ζ).map rationalSparseIntervalPackOutput)

theorem rational_interval_sparse_initialized_origin {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) (ζ : ℚ) (o : RationalIntervalRationalOutput k m)
    (hout : rationalIntervalSparseInitialized d ζ=some o) :
    ∃ model, rationalIntervalInitialize d=some model ∧
      ∃ z w, rationalIntervalSparseAccurate model ζ=some (z,w) ∧
        o=rationalSparseIntervalPackOutput (z,w) := by
  cases hm : rationalIntervalInitialize d with
  | none => simp only [rationalIntervalSparseInitialized,hm,Option.bind_none] at hout; cases hout
  | some model =>
    cases ha : rationalIntervalSparseAccurate model ζ with
    | none => simp only [rationalIntervalSparseInitialized,hm,Option.bind_some,ha,Option.map_none] at hout; cases hout
    | some w =>
      have he : rationalSparseIntervalPackOutput w=o := Option.some.inj
        (by simpa only [rationalIntervalSparseInitialized,hm,Option.bind_some,ha,Option.map_some] using hout)
      exact ⟨model,rfl,w.1,w.2,ha,he.symm⟩

theorem rational_interval_sparse_initialized_complete {k m : ℕ} {I : Type} [Fintype I]
    (d : RationalIntervalParameters k m I) (ζ : ℚ) (hc : d.Compatible) :
    ∃ o, rationalIntervalSparseInitialized d ζ=some o := by
  obtain ⟨z,w,hout⟩ := rational_interval_sparse_accurate_complete (d.toModel hc) ζ
  exact ⟨rationalSparseIntervalPackOutput (z,w),by
    simp only [rationalIntervalSparseInitialized,rational_interval_initialize_complete d hc,
      Option.bind_some,hout,Option.map_some]⟩

theorem rational_interval_sparse_initialized_none_iff {k m : ℕ} {I : Type} [Fintype I]
    (d : RationalIntervalParameters k m I) (ζ : ℚ) :
    rationalIntervalSparseInitialized d ζ=none ↔ ¬d.Compatible := by
  constructor
  · intro hn hc
    obtain ⟨o,ho⟩ := rational_interval_sparse_initialized_complete d ζ hc
    rw [hn] at ho
    cases ho
  · intro hn
    have hi := (rational_interval_initialize_none_iff d).mpr hn
    simp only [rationalIntervalSparseInitialized,hi,Option.bind_none]

theorem rational_interval_sparse_initialized_game {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) (ζ : ℚ) (o : RationalIntervalRationalOutput k m)
    (hout : rationalIntervalSparseInitialized d ζ=some o) :
    ∃ hc : d.Compatible,
      o.realData ∈ intervalGameClass (d.toModel hc) ∧
      (∀ a, response (intervalGameMatrix o.realData) (intervalGameWeights (d.toModel hc) o.realData) a ≤
        (o.bracket.2 : ℝ)+(d.η : ℝ)) ∧
      (Finset.univ.filter fun i => o.q i ≠ 0).card ≤
        min m (k+rationalGridSize d.M d.r d.η+Fintype.card I+1) := by
  obtain ⟨model,hm,z,w,ha,rfl⟩ := rational_interval_sparse_initialized_origin d ζ o hout
  obtain ⟨hc,he⟩ := rational_interval_initialize_sound d model hm
  subst model
  have hAlg := (rational_interval_sparse_approximation_origin (d.toModel hc)
    (rationalLogRounds d.M ζ) z w ha).2
  exact ⟨hc,rational_interval_sparse_algorithm_game (d.toModel hc) z.2
    w.1 w.2.1 w.2.2.1 w.2.2.2 hAlg⟩

theorem rational_interval_sparse_initialized_value {k m : ℕ} {I : Type*} [Fintype I]
    [Nonempty (Fin k ⊕ Fin m)] (d : RationalIntervalParameters k m I)
    (ζ : ℚ) (hζ : 0 < ζ) (o : RationalIntervalRationalOutput k m)
    (hout : rationalIntervalSparseInitialized d ζ=some o) :
    ∃ hc : d.Compatible,
      (o.bracket.1 : ℝ) ≤ intervalGameValue (d.toModel hc) ∧
      intervalGameValue (d.toModel hc) ≤ (o.bracket.2 : ℝ)+(d.η : ℝ) ∧
      (o.bracket.2 : ℝ)+(d.η : ℝ)-(o.bracket.1 : ℝ) < (d.η : ℝ)+(ζ : ℝ) := by
  obtain ⟨model,hm,z,w,ha,rfl⟩ := rational_interval_sparse_initialized_origin d ζ o hout
  obtain ⟨hc,he⟩ := rational_interval_initialize_sound d model hm
  subst model
  exact ⟨hc,rational_interval_sparse_accurate_value_enclosure (d.toModel hc) ζ hζ z w ha⟩

end SparseCompletion
