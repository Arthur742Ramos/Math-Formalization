/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import ProtectedSources.RationalIntervalOutputClass
@[expose] public section
namespace SparseCompletion

theorem rational_interval_approximation_output {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalModel k m I) (n : ℕ) (z : ℚ × ℚ)
    (x : Fin (m+(m*k+(k*k+rationalGridSize d.M d.r d.η*m))) → ℚ) (B : Fin m → Fin m → ℚ)
    (h : rationalIntervalApproximation d.loK d.hiK d.lo d.hi d.p d.M d.r d.η d.R n=some (z,(x,B))) :
    z=rationalIntervalSearch d.loK d.hiK d.lo d.hi d.p d.M d.r d.η d.R n ∧
    rationalIntervalRepertoireAlgorithm d.loK d.hiK d.lo d.hi d.p d.M d.r z.2 d.η d.R=some (x,B) := by
  cases ha : rationalIntervalRepertoireAlgorithm d.loK d.hiK d.lo d.hi d.p d.M d.r
    (rationalIntervalSearch d.loK d.hiK d.lo d.hi d.p d.M d.r d.η d.R n).2 d.η d.R with
  | none => simp only [rationalIntervalApproximation,ha,Option.map_none] at h; cases h
  | some w =>
    have he := Option.some.inj (by simpa only [rationalIntervalApproximation,ha,Option.map_some] using h)
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
    exact ⟨rfl,ha⟩

theorem rational_interval_approximation_value_enclosure {k m : ℕ} {I : Type*} [Fintype I]
    [Nonempty (Fin k ⊕ Fin m)] (d : RationalIntervalModel k m I) (n : ℕ) (z : ℚ × ℚ)
    (x : Fin (m+(m*k+(k*k+rationalGridSize d.M d.r d.η*m))) → ℚ) (B : Fin m → Fin m → ℚ)
    (hout : rationalIntervalApproximation d.loK d.hiK d.lo d.hi d.p d.M d.r d.η d.R n=some (z,(x,B))) :
    (z.1 : ℝ) ≤ intervalGameValue d ∧ intervalGameValue d ≤ (z.2 : ℝ)+(d.η : ℝ) ∧
      z.2-z.1 ≤ d.M/((2 : ℕ) : ℚ)^n := by
  obtain ⟨hz,ha⟩ := rational_interval_approximation_output d n z x B hout
  have hbr := rational_interval_search_bracket d.loK d.hiK d.lo d.hi d.p d.M d.r d.η d.R n
    (le_of_lt d.positiveBound) (rational_interval_model_upper_feasible d)
  rw [←hz] at hbr
  have hclass := rational_interval_algorithm_output_class d z.2 x B ha
  have hfull := rational_interval_repertoire_algorithm_full_game d.loK d.hiK d.lo d.hi d.p
    d.M d.r z.2 d.η d.R d.positiveSlack d.anchorNonneg d.normalized d.coreLower d.coreUpper
    d.crossLower d.crossUpper d.orderedCross x B ha
  rcases hfull with ⟨_,_,_,_,_,_,_,hrows⟩
  have hu : intervalGameValue d ≤ (z.2 : ℝ)+(d.η : ℝ) := by
    apply le_trans (interval_game_value_le_witness d _ hclass)
    apply (exploitability_le_iff _ _ _).mpr
    exact hrows
  refine ⟨?_,hu,hbr.2.2.2.2.2⟩
  rcases hbr.2.2.2.2.1 with hzero | hno
  · rw [hzero,Rat.cast_zero]
    exact (interval_game_value_bounds d).1
  · by_contra hlow
    have hvL : intervalGameValue d ≤ (z.1 : ℝ) := le_of_lt (lt_of_not_ge hlow)
    obtain ⟨w,hw,he⟩ := interval_game_value_attained d
    rcases hw with ⟨⟨⟨hq,_⟩,⟨hDl,hDu⟩,⟨hKl,hKu⟩,hB,hBb⟩,hm,hK,hR⟩
    have hr : ∀ a, response (blockMatrix w.2.2.1 w.2.1 w.2.2.2)
        (blockWeights (fun a => (d.p a : ℝ)) w.1) a ≤ (z.1 : ℝ) := by
      intro a
      exact le_trans (response_le_exploitability _ _ a) (le_trans he.le hvL)
    obtain ⟨y,C,hC⟩ := real_interval_repertoire_algorithm_success d.loK d.hiK d.lo d.hi d.p
      d.M d.r z.1 d.η d.R w.2.2.1 w.2.1 w.1 w.2.2.2 d.positiveBound d.positiveSlack
      d.orderedCross d.anchorNonneg hq hm hK (fun a b => ⟨hKl a b,hKu a b⟩)
      (fun i a => ⟨hDl i a,hDu i a⟩) hB hBb hr hR
    obtain ⟨hpoint,hRy,_⟩ := rational_interval_repertoire_algorithm_output d.loK d.hiK d.lo d.hi
      d.p d.M d.r z.1 d.η d.R y C hC
    exact hno ⟨y,(rational_interval_repertoire_system_iff d.loK d.hiK d.lo d.hi d.p d.M d.r z.1 d.η d.R y).mpr
      ⟨(rational_interval_system_point d.loK d.hiK d.lo d.hi d.p d.M d.r z.1 d.η y).mpr hpoint,hRy⟩⟩

end SparseCompletion
