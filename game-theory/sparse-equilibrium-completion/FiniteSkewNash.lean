/- AI-assisted formalization under the repository Apache-2.0 license.
Both-player mixed-deviation interpretation of the finite skew-game row
criterion. This is classical zero-sum background, not a new algorithm result. -/
module
public import FiniteSkewEquilibrium
@[expose] public section
open scoped BigOperators
namespace SparseCompletion

def zeroSumPayoff {ι : Type*} [Fintype ι] (A : ι → ι → ℝ)
    (p q : ι → ℝ) : ℝ := ∑ i, p i*response A q i

/-- The first player's reward is zeroSumPayoff and the second player's reward
is its negative. Both players may deviate to any normalized mixed strategy. -/
def symmetricApproximateNash {ι : Type*} [Fintype ι]
    (A : ι → ι → ℝ) (q : ι → ℝ) (ε : ℝ) : Prop :=
  q ∈ finiteGameSimplex ∧
  (∀ x, x ∈ finiteGameSimplex → zeroSumPayoff A x q ≤ zeroSumPayoff A q q+ε) ∧
  ∀ y, y ∈ finiteGameSimplex → -zeroSumPayoff A q y ≤ -zeroSumPayoff A q q+ε

theorem zero_sum_payoff_skew {ι : Type*} [Fintype ι]
    (A : ι → ι → ℝ) (hA : IsSkew A) (p q : ι → ℝ) :
    zeroSumPayoff A p q= -zeroSumPayoff A q p := by
  unfold zeroSumPayoff response
  simp only [Finset.mul_sum]
  rw [← Finset.sum_neg_distrib,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [hA j i]
  ring

theorem zero_sum_payoff_self_zero {ι : Type*} [Fintype ι]
    (A : ι → ι → ℝ) (hA : IsSkew A) (q : ι → ℝ) :
    zeroSumPayoff A q q=0 := finite_skew_self_response_zero A hA q

theorem finite_game_simplex_pure {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    Pi.single i (1 : ℝ) ∈ finiteGameSimplex := by
  constructor
  · intro j
    simp only [Pi.single_apply]
    split <;> norm_num
  · simp

theorem finite_mixed_deviation_bound {ι : Type*} [Fintype ι]
    (A : ι → ι → ℝ) (q x : ι → ℝ) (ε : ℝ)
    (hx : x ∈ finiteGameSimplex) (hrows : ∀ i, response A q i ≤ ε) :
    zeroSumPayoff A x q ≤ ε := by
  calc
    _ ≤ ∑ i, x i*ε := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hrows i) (hx.1 i))
    _ = ε := by rw [← Finset.sum_mul,hx.2,one_mul]

theorem finite_skew_nash_iff_rows {ι : Type*} [Fintype ι]
    (A : ι → ι → ℝ) (hA : IsSkew A) (q : ι → ℝ) (ε : ℝ) :
    symmetricApproximateNash A q ε ↔
      q ∈ finiteGameSimplex ∧ ∀ i, response A q i ≤ ε := by
  classical
  have hz := zero_sum_payoff_self_zero A hA q
  constructor
  · rintro ⟨hq,hfirst,_⟩
    refine ⟨hq,?_⟩
    intro i
    have hh := hfirst (Pi.single i 1) (finite_game_simplex_pure i)
    rw [hz,zero_add] at hh
    simpa [zeroSumPayoff,Pi.single_apply] using hh
  · rintro ⟨hq,hrows⟩
    refine ⟨hq,?_,?_⟩
    · intro x hx
      rw [hz,zero_add]
      exact finite_mixed_deviation_bound A q x ε hx hrows
    · intro y hy
      rw [zero_sum_payoff_skew A hA q y,neg_neg,hz,neg_zero,zero_add]
      exact finite_mixed_deviation_bound A q y ε hy hrows

theorem finite_skew_symmetric_nash_exists {ι : Type*} [Fintype ι] [Nonempty ι]
    (A : ι → ι → ℝ) (hA : IsSkew A) :
    ∃ q : ι → ℝ, symmetricApproximateNash A q 0 := by
  obtain ⟨q,hq,hm,hr⟩ := finite_skew_equilibrium_exists A hA
  exact ⟨q,(finite_skew_nash_iff_rows A hA q 0).mpr ⟨⟨hq,hm⟩,hr⟩⟩

end SparseCompletion
