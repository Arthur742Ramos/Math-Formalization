/- AI-assisted formalization under the repository Apache-2.0 license.
Sparse actual witnesses at the original interval bisection bracket. -/
module
public import ProtectedSources.RationalIntervalSparseGame
public import ProtectedSources.RationalIntervalAccurate
@[expose] public section
namespace SparseCompletion

def rationalIntervalSparseApproximation {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalModel k m I) (n : ℕ) :
    Option ((ℚ × ℚ) × RationalSparseIntervalData k m) :=
  let z := rationalIntervalSearch d.loK d.hiK d.lo d.hi d.p d.M d.r d.η d.R n
  (rationalIntervalSparseAlgorithm d.loK d.hiK d.lo d.hi d.p d.M d.r z.2 d.η d.R).map
    (fun w => (z,w))

theorem rational_interval_sparse_approximation_origin {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalModel k m I) (n : ℕ) (z : ℚ × ℚ) (w : RationalSparseIntervalData k m)
    (hout : rationalIntervalSparseApproximation d n=some (z,w)) :
    z=rationalIntervalSearch d.loK d.hiK d.lo d.hi d.p d.M d.r d.η d.R n ∧
      rationalIntervalSparseAlgorithm d.loK d.hiK d.lo d.hi d.p d.M d.r z.2 d.η d.R=some w := by
  cases ha : rationalIntervalSparseAlgorithm d.loK d.hiK d.lo d.hi d.p d.M d.r
    (rationalIntervalSearch d.loK d.hiK d.lo d.hi d.p d.M d.r d.η d.R n).2 d.η d.R with
  | none => simp only [rationalIntervalSparseApproximation,ha,Option.map_none] at hout; cases hout
  | some v =>
    have he := Option.some.inj (by
      simpa only [rationalIntervalSparseApproximation,ha,Option.map_some] using hout)
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
    exact ⟨rfl,ha⟩

theorem rational_interval_sparse_approximation_complete {k m : ℕ} {I : Type} [Fintype I]
    (d : RationalIntervalModel k m I) (n : ℕ) :
    ∃ z w, rationalIntervalSparseApproximation d n=some (z,w) := by
  have hz := rational_interval_search_bracket d.loK d.hiK d.lo d.hi d.p d.M d.r d.η d.R n
    (le_of_lt d.positiveBound) (rational_interval_model_upper_feasible d)
  let z := rationalIntervalSearch d.loK d.hiK d.lo d.hi d.p d.M d.r d.η d.R n
  obtain ⟨w,hw⟩ := rational_interval_sparse_algorithm_real_complete d.loK d.hiK d.lo d.hi d.p
    d.M d.r z.2 d.η d.R d.positiveBound d.positiveSlack d.orderedCross
    ((rational_linear_real_feasible_iff _).mpr hz.2.2.2.1)
  dsimp only [z] at hw
  exact ⟨z,w,by simp only [rationalIntervalSparseApproximation,hw,Option.map_some,z]⟩

theorem rational_interval_sparse_approximation_value_enclosure {k m : ℕ} {I : Type*} [Fintype I]
    [Nonempty (Fin k ⊕ Fin m)] (d : RationalIntervalModel k m I) (n : ℕ)
    (z : ℚ × ℚ) (w : RationalSparseIntervalData k m)
    (hout : rationalIntervalSparseApproximation d n=some (z,w)) :
    (z.1 : ℝ) ≤ intervalGameValue d ∧ intervalGameValue d ≤ (z.2 : ℝ)+(d.η : ℝ) ∧
      z.2-z.1 ≤ d.M/((2 : ℕ) : ℚ)^n := by
  have hz := (rational_interval_sparse_approximation_origin d n z w hout).1
  obtain ⟨z',x,B,ha⟩ := rational_interval_model_approximation_complete d n
  have hz' := (rational_interval_approximation_output d n z' x B ha).1
  have hb := rational_interval_approximation_value_enclosure d n z' x B ha
  rw [hz',←hz] at hb
  exact hb

def rationalIntervalSparseAccurate {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalModel k m I) (ζ : ℚ) :=
  rationalIntervalSparseApproximation d (rationalLogRounds d.M ζ)

theorem rational_interval_sparse_accurate_complete {k m : ℕ} {I : Type} [Fintype I]
    (d : RationalIntervalModel k m I) (ζ : ℚ) :
    ∃ z w, rationalIntervalSparseAccurate d ζ=some (z,w) :=
  rational_interval_sparse_approximation_complete d (rationalLogRounds d.M ζ)

theorem rational_interval_sparse_accurate_value_enclosure {k m : ℕ} {I : Type*} [Fintype I]
    [Nonempty (Fin k ⊕ Fin m)] (d : RationalIntervalModel k m I) (ζ : ℚ) (hζ : 0 < ζ)
    (z : ℚ × ℚ) (w : RationalSparseIntervalData k m)
    (hout : rationalIntervalSparseAccurate d ζ=some (z,w)) :
    (z.1 : ℝ) ≤ intervalGameValue d ∧ intervalGameValue d ≤ (z.2 : ℝ)+(d.η : ℝ) ∧
      (z.2 : ℝ)+(d.η : ℝ)-(z.1 : ℝ) < (d.η : ℝ)+(ζ : ℝ) := by
  have hb := rational_interval_sparse_approximation_value_enclosure d (rationalLogRounds d.M ζ) z w hout
  have hw : z.2-z.1 < ζ := lt_of_le_of_lt hb.2.2 (rational_log_rounds_width d.M ζ hζ)
  have hwR : (z.2 : ℝ)-(z.1 : ℝ) < (ζ : ℝ) := by exact_mod_cast hw
  exact ⟨hb.1,hb.2.1,by linarith⟩

end SparseCompletion
