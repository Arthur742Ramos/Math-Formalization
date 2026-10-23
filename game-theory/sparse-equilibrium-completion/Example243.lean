/- AI-assisted formalization under the repository Apache-2.0 license.
Separate source draft: the authenticated paper's equal odd-bin core example.
This instantiates existing Lean payoff/weight mathematics. It makes no claim
about prototype implementation fidelity or minimality of the eleven actions. -/
module
public import ExplicitBinnedCore
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def example243Lengths : Fin 9 → ℕ := fun _ => 27

theorem example243_lengths_positive (b : Fin 9) : 0 < example243Lengths b := by
  norm_num [example243Lengths]

theorem example243_residual_count : (∑ b, example243Lengths b)=243 := by
  norm_num [example243Lengths]

def example243WeightsQ : Fin (∑ b, example243Lengths b) → ℚ :=
  rationalBinnedWeights example243Lengths example243_lengths_positive (1/4)

def example243PayoffQ : Fin (∑ b, example243Lengths b) → Fin (∑ b, example243Lengths b) → ℚ :=
  rationalExplicitBinPayoff example243Lengths

def example243FullWeightsQ : (Fin 2 ⊕ Fin (∑ b, example243Lengths b)) → ℚ :=
  Sum.elim (fun _ => 3/8) example243WeightsQ

def example243ErrorQ : ℚ :=
  (1/4 : ℚ)^2/(12*(243 : ℚ)^3)*(9*(27 : ℚ)*((27 : ℚ)^2-1))

def example243CoreChangeQ : ℚ := (8/3 : ℚ)*example243ErrorQ

theorem example243_error_rational : example243ErrorQ=91/1417176 := by
  norm_num [example243ErrorQ]

theorem example243_core_change_rational : example243CoreChangeQ=91/531441 := by
  norm_num [example243CoreChangeQ, example243ErrorQ]

theorem example243_core_change_within_radius : example243CoreChangeQ < (1/5000 : ℚ) := by
  rw [example243_core_change_rational]
  norm_num

noncomputable section

def example243Weights : Fin (∑ b, example243Lengths b) → ℝ :=
  binnedWeights example243Lengths example243_lengths_positive (1/(4 : ℕ))

def example243Payoff : Fin (∑ b, example243Lengths b) → Fin (∑ b, example243Lengths b) → ℝ :=
  explicitBinnedMatrix example243Lengths

theorem example243_weights_real (i : Fin (∑ b, example243Lengths b)) :
    (example243WeightsQ i : ℝ)=example243Weights i := by
  simpa only [example243WeightsQ, example243Weights, Rat.cast_div, Rat.cast_one,
    Rat.cast_ofNat, Nat.cast_ofNat] using rational_binned_weights_real example243Lengths
      example243_lengths_positive (1/4) i

theorem example243_payoff_real (i j : Fin (∑ b, example243Lengths b)) :
    (example243PayoffQ i j : ℝ)=example243Payoff i j := rfl

theorem example243_full_weights_real (v : Fin 2 ⊕ Fin (∑ b, example243Lengths b)) :
    (example243FullWeightsQ v : ℝ)=
      blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) example243Weights v := by
  cases v with
  | inl a => norm_num [example243FullWeightsQ, blockWeights, twoShares]
  | inr i => exact example243_weights_real i

theorem example243_error : explicitBinnedError example243Lengths=(91/1417176 : ℝ) := by
  norm_num [explicitBinnedError, example243Lengths, binParityTerm]

theorem example243_error_real : (example243ErrorQ : ℝ)=explicitBinnedError example243Lengths := by
  rw [example243_error_rational, example243_error]
  norm_num

theorem example243_action_count : Fintype.card (Fin 2 ⊕ Fin (∑ b, example243Lengths b))=245 := by
  simp only [Fintype.card_sum, Fintype.card_fin, example243_residual_count]

theorem example243_residual_support : supportSize example243Weights=9 := by
  exact binned_odd_support_exact example243Lengths example243_lengths_positive
    (by rw [example243_residual_count]; norm_num)
    (by intro b; norm_num [example243Lengths]) (1/(4 : ℕ)) (by norm_num)


/-- The numerical error is the actual central game's anchor response, with
opposite error at the other anchor and zero response on every residual row. -/
theorem example243_central_responses :
    let m := ∑ b, example243Lengths b
    let A := blockMatrix (rigidityCore (uniformTarget m (1/(4 : ℕ))))
      (rigidityCross (uniformTarget m (1/(4 : ℕ)))) example243Payoff
    let x := blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) example243Weights
    response A x (.inl 0)=(91/1417176 : ℝ) ∧
      response A x (.inl 1)= -(91/1417176 : ℝ) ∧ ∀ j, response A x (.inr j)=0 := by
  obtain ⟨d, _, _, _, _, _, _, _, _, h0, h1, hrows, he⟩ :=
    explicit_binned_game_witness example243Lengths example243_lengths_positive
      (by rw [example243_residual_count]; norm_num)
  have hd : d=(91/1417176 : ℝ) := by
    change d=explicitBinnedError example243Lengths at he
    rw [example243_error] at he
    exact he
  rw [hd] at h0 h1
  exact ⟨h0, h1, hrows⟩

/-- The existing explicit construction, with the literal core-only interval
predicate and original bin labels. The two anchor shares are exactly 3/8. -/
theorem example243_core_witness :
    ∃ u, UniformCoreWitness (∑ b, example243Lengths b) 0 (1/5000)
      example243Weights u example243Payoff := by
  apply explicit_binned_core_witness example243Lengths example243_lengths_positive
    (by rw [example243_residual_count]; norm_num) 0 (1/5000) (by norm_num) (by norm_num)
  rw [example243_error]
  norm_num

theorem example243_total_support :
    (Finset.univ.filter fun v =>
      blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) example243Weights v ≠ 0).card=11 := by
  obtain ⟨u, hu⟩ := example243_core_witness
  have hs := uniform_interval_total_support_card (by norm_num : (0 : ℝ) ≤ 1/5000) hu
  rw [example243_residual_support] at hs
  exact hs

theorem example243_rational_total_support :
    (Finset.univ.filter fun v => example243FullWeightsQ v ≠ 0).card=11 := by
  have hsupport : (Finset.univ.filter fun v => example243FullWeightsQ v ≠ 0)=
      (Finset.univ.filter fun v =>
        blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) example243Weights v ≠ 0) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ←example243_full_weights_real,
      Rat.cast_ne_zero]
  rw [hsupport]
  exact example243_total_support

/-- At exact tolerance the two opposite anchor inequalities pin the core
decrease. Its numerical value is earned from the actual supplied bin game. -/
theorem example243_witness_core_change (u : ℝ)
    (hu : UniformCoreWitness (∑ b, example243Lengths b) 0 (1/5000)
      example243Weights u example243Payoff) :
    uniformCoreValue (∑ b, example243Lengths b)-u=(91/531441 : ℝ) := by
  obtain ⟨h0, h1, _⟩ := example243_central_responses
  let m := ∑ b, example243Lengths b
  let D := rigidityCross (uniformTarget m (1/(4 : ℕ)))
  change response (blockMatrix (twoCore (uniformCoreValue m)) D example243Payoff)
    (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) example243Weights) (.inl 0)=(91/1417176 : ℝ) at h0
  change response (blockMatrix (twoCore (uniformCoreValue m)) D example243Payoff)
    (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) example243Weights) (.inl 1)= -(91/1417176 : ℝ) at h1
  have hshift := two_core_anchor_shift D example243Payoff example243Weights
    (uniformCoreValue m) (((3 : ℕ) : ℝ)/(8 : ℕ)*(uniformCoreValue m-u))
  have hnew : uniformCoreValue m-(((8 : ℕ) : ℝ)/(3 : ℕ))*
      ((((3 : ℕ) : ℝ)/(8 : ℕ))*(uniformCoreValue m-u))=u := by ring
  rw [hnew, h0, h1] at hshift
  obtain ⟨_, _, _, _, _, _, _, _, _, hresp⟩ := hu
  have ha := hresp (.inl 0)
  have hb := hresp (.inl 1)
  change response (blockMatrix (twoCore u) D example243Payoff)
    (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) example243Weights) (.inl 0) ≤ 0 at ha
  change response (blockMatrix (twoCore u) D example243Payoff)
    (blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ))) example243Weights) (.inl 1) ≤ 0 at hb
  change uniformCoreValue m-u=(91/531441 : ℝ)
  norm_num only [Nat.cast_ofNat] at hshift
  linarith [hshift.1, hshift.2]

/-- A feasible eleven-action witness in the source's 245-label game. This
asserts existence and exact compatibility, without a support-minimality claim. -/
theorem example243_eleven_action_witness :
    Fintype.card (Fin 2 ⊕ Fin (∑ b, example243Lengths b))=245 ∧
      ∃ u, UniformCoreWitness (∑ b, example243Lengths b) 0 (1/5000)
        example243Weights u example243Payoff ∧
        (Finset.univ.filter fun v => blockWeights (twoShares (((3 : ℕ) : ℝ)/(4 : ℕ)))
          example243Weights v ≠ 0).card=11 ∧
        uniformCoreValue (∑ b, example243Lengths b)-u=(91/531441 : ℝ) ∧
        |u-uniformCoreValue (∑ b, example243Lengths b)| < (1/5000 : ℝ) := by
  obtain ⟨u, hu⟩ := example243_core_witness
  have hchange := example243_witness_core_change u hu
  refine ⟨example243_action_count, u, hu, example243_total_support, hchange, ?_⟩
  have habs : |u-uniformCoreValue (∑ b, example243Lengths b)|=(91/531441 : ℝ) := by
    rw [abs_sub_comm, hchange]
    norm_num
  rw [habs]
  norm_num

end
end SparseCompletion
