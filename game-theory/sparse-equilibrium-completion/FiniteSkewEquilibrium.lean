/- AI-assisted formalization. Released under the repository Apache-2.0 license.
Human formalization authorship and maintainer membership remain unconfirmed.
Existence for arbitrary finite nonempty real skew games,
using genuine compact/closed separation, without a minimax or LP oracle. -/
module
public import CompletionGeometry

@[expose] public section
open scoped BigOperators
open Set

namespace SparseCompletion
noncomputable section

/-- The literal probability simplex; avoids deprecated `stdSimplex` APIs. -/
def finiteGameSimplex {ι : Type*} [Fintype ι] : Set (ι → ℝ) :=
  {q | (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1}

theorem finite_game_simplex_closed {ι : Type*} [Fintype ι] :
    IsClosed (finiteGameSimplex (ι := ι)) := by
  have he : finiteGameSimplex (ι := ι) =
      (⋂ i, {q : ι → ℝ | 0 ≤ q i}) ∩ {q | ∑ i, q i = 1} := by
    ext q
    simp only [finiteGameSimplex, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [he]
  apply IsClosed.inter
  · exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  · exact isClosed_eq (by fun_prop) continuous_const

theorem finite_game_simplex_compact {ι : Type*} [Fintype ι] :
    IsCompact (finiteGameSimplex (ι := ι)) := by
  apply IsCompact.of_isClosed_subset (s := Set.Icc (0 : ι → ℝ) 1)
    isCompact_Icc finite_game_simplex_closed
  intro q hq
  refine ⟨hq.1, ?_⟩
  intro i
  calc
    q i ≤ ∑ j, q j := Finset.single_le_sum (fun j _ => hq.1 j) (Finset.mem_univ i)
    _ = 1 := hq.2

theorem finite_game_simplex_convex {ι : Type*} [Fintype ι] :
    Convex ℝ (finiteGameSimplex (ι := ι)) := by
  intro q hq w hw a b ha hb hab
  constructor
  · intro i
    change 0 ≤ a*q i+b*w i
    exact add_nonneg (mul_nonneg ha (hq.1 i)) (mul_nonneg hb (hw.1 i))
  · change (∑ i, (a*q i+b*w i)) = 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hq.2, hw.2]
    simpa only [mul_one] using hab

theorem finite_game_simplex_nonempty {ι : Type*} [Fintype ι] [Nonempty ι] :
    (finiteGameSimplex (ι := ι)).Nonempty := by
  classical
  let i : ι := Classical.choice inferInstance
  refine ⟨Pi.single i 1, ?_, ?_⟩
  · intro j
    simp only [Pi.single_apply]
    split <;> norm_num
  · simp

/-- Linear map to the negated vector of all original responses. -/
def finiteNegGameResponse {ι : Type*} [Fintype ι] (A : ι → ι → ℝ) :
    (ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun q i := -response A q i
  map_add' q w := by
    ext i
    simp only [response, Pi.add_apply, mul_add, Finset.sum_add_distrib, neg_add]
  map_smul' a q := by
    ext i
    change -(∑ j, A i j*(a*q j)) = a*(-∑ j, A i j*q j)
    rw [mul_neg, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- Skewness alone cancels the self-payoff; no sign or normalization assumption. -/
theorem finite_skew_self_response_zero {ι : Type*} [Fintype ι]
    (A : ι → ι → ℝ) (hA : IsSkew A) (q : ι → ℝ) :
    (∑ i, q i*response A q i) = 0 := by
  simpa only [response, Finset.mul_sum, mul_assoc] using
    skew_weighted_sum Finset.univ q A hA

/-- Every finite nonempty real skew-symmetric game has an exact mixed strategy
    whose every original action response is nonpositive. No payoff bound needed. -/
theorem finite_skew_equilibrium_exists {ι : Type*} [Fintype ι] [Nonempty ι]
    (A : ι → ι → ℝ) (hA : IsSkew A) :
    ∃ q : ι → ℝ, (∀ i, 0 ≤ q i) ∧ (∑ i, q i = 1) ∧
      ∀ i, response A q i ≤ 0 := by
  classical
  let T : Set (ι → ℝ) := finiteNegGameResponse A '' finiteGameSimplex
  have hTcompact : IsCompact T :=
    finite_game_simplex_compact.image (finiteNegGameResponse A).continuous_of_finiteDimensional
  have hTconvex : Convex ℝ T :=
    finite_game_simplex_convex.linear_image (finiteNegGameResponse A)
  have hinter : (T ∩ upperOrthant (0 : ι → ℝ)).Nonempty := by
    by_contra hn
    have hdisj : Disjoint T (upperOrthant (0 : ι → ℝ)) := by
      rw [Set.disjoint_iff_inter_eq_empty]
      exact Set.not_nonempty_iff_eq_empty.mp hn
    obtain ⟨f, u, w, hleft, huw, hright⟩ :=
      geometric_hahn_banach_compact_closed hTconvex hTcompact
        (upperOrthant_convex (0 : ι → ℝ)) (upperOrthant_closed (0 : ι → ℝ)) hdisj
    let y : ι → ℝ := fun i => f (Pi.single i 1)
    have hy : ∀ i, 0 ≤ y i :=
      separator_coefficients_nonnegative (0 : ι → ℝ) f w hright
    let S : ℝ := ∑ i, y i
    have hSnonneg : 0 ≤ S := Finset.sum_nonneg (fun i _ => hy i)
    have hS : 0 < S := by
      by_contra hnS
      have hSzero : S = 0 := le_antisymm (le_of_not_gt hnS) hSnonneg
      have hyzero : ∀ i, y i = 0 := by
        intro i
        apply le_antisymm _ (hy i)
        calc
          y i ≤ ∑ j, y j := Finset.single_le_sum (fun j _ => hy j) (Finset.mem_univ i)
          _ = 0 := hSzero
      have hfzero : ∀ z : ι → ℝ, f z = 0 := by
        intro z
        rw [dual_evaluation]
        change (∑ i, y i*z i) = 0
        simp only [hyzero, zero_mul, Finset.sum_const_zero]
      obtain ⟨q0, hq0⟩ := finite_game_simplex_nonempty (ι := ι)
      have hl := hleft (finiteNegGameResponse A q0) ⟨q0, hq0, rfl⟩
      have hr := hright (0 : ι → ℝ) (fun _ => le_rfl)
      rw [hfzero] at hl hr
      linarith
    let q : ι → ℝ := fun i => y i/S
    have hq : q ∈ finiteGameSimplex := by
      constructor
      · intro i
        exact div_nonneg (hy i) (le_of_lt hS)
      · change (∑ i, y i/S) = 1
        rw [← Finset.sum_div]
        exact div_self (ne_of_gt hS)
    have hweighted := finite_skew_self_response_zero A hA q
    have hfq : f (finiteNegGameResponse A q) = 0 := by
      rw [dual_evaluation]
      change (∑ i, y i*(-response A q i)) = 0
      have he : ∀ i, y i*(-response A q i) = -S*(q i*response A q i) := by
        intro i
        dsimp [q]
        field_simp [ne_of_gt hS]
      simp only [he, ← Finset.mul_sum, hweighted, mul_zero]
    have hl := hleft (finiteNegGameResponse A q) ⟨q, hq, rfl⟩
    have hr := hright (0 : ι → ℝ) (fun _ => le_rfl)
    rw [hfq] at hl
    rw [map_zero] at hr
    linarith
  obtain ⟨z, ⟨q, hq, hz⟩, hnonneg⟩ := hinter
  refine ⟨q, hq.1, hq.2, ?_⟩
  intro i
  have hi := hnonneg i
  rw [← hz] at hi
  change 0 ≤ -response A q i at hi
  linarith

end
end SparseCompletion
