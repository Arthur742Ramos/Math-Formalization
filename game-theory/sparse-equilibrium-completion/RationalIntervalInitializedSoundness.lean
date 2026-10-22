/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed. -/
module
public import RationalIntervalInitializedAlgorithm
@[expose] public section
namespace SparseCompletion
noncomputable section

def RationalIntervalRationalOutput.realData {k m : ℕ} (o : RationalIntervalRationalOutput k m) :
    IntervalGameData k m :=
  (fun i => (o.q i : ℝ),fun i a => (o.D i a : ℝ),
    fun a b => (o.K a b : ℝ),fun i j => (o.B i j : ℝ))

theorem rational_interval_initialized_game {k m : ℕ} {I : Type*} [Fintype I]
    (d : RationalIntervalParameters k m I) (ζ : ℚ) (o : RationalIntervalRationalOutput k m)
    (hout : rationalIntervalInitializedApproximation d ζ=some o) :
    ∃ hc : d.Compatible,
      o.realData ∈ intervalGameClass (d.toModel hc) ∧
      ∀ a, response (intervalGameMatrix o.realData) (intervalGameWeights (d.toModel hc) o.realData) a ≤
        (o.bracket.2 : ℝ)+(d.η : ℝ) := by
  obtain ⟨model,hm,z,x,B,ha,rfl⟩ := rational_interval_initialized_output d ζ o hout
  obtain ⟨hc,he⟩ := rational_interval_initialize_sound d model hm
  subst model
  have hAlg := (rational_interval_approximation_output (d.toModel hc)
    (rationalLogRounds d.M ζ) z x B ha).2
  have hClass := rational_interval_algorithm_output_class (d.toModel hc) z.2 x B hAlg
  have hGame := rational_interval_repertoire_algorithm_full_game d.loK d.hiK d.lo d.hi d.p
    d.M d.r z.2 d.η d.R d.positiveSlack d.anchorNonneg d.normalized d.coreLower d.coreUpper
    d.crossLower d.crossUpper d.orderedCross x B hAlg
  rcases hGame with ⟨_,_,_,_,_,_,_,hrows⟩
  exact ⟨hc,hClass,hrows⟩

theorem rational_interval_initialized_value {k m : ℕ} {I : Type*} [Fintype I]
    [Nonempty (Fin k ⊕ Fin m)] (d : RationalIntervalParameters k m I)
    (ζ : ℚ) (hζ : 0 < ζ) (o : RationalIntervalRationalOutput k m)
    (hout : rationalIntervalInitializedApproximation d ζ=some o) :
    ∃ hc : d.Compatible,
      (o.bracket.1 : ℝ) ≤ intervalGameValue (d.toModel hc) ∧
      intervalGameValue (d.toModel hc) ≤ (o.bracket.2 : ℝ)+(d.η : ℝ) ∧
      (o.bracket.2 : ℝ)+(d.η : ℝ)-(o.bracket.1 : ℝ) < (d.η : ℝ)+(ζ : ℝ) := by
  obtain ⟨model,hm,z,x,B,ha,rfl⟩ := rational_interval_initialized_output d ζ o hout
  obtain ⟨hc,he⟩ := rational_interval_initialize_sound d model hm
  subst model
  exact ⟨hc,rational_interval_accurate_value_enclosure (d.toModel hc) ζ hζ z x B ha⟩

end
end SparseCompletion
