module

public import BoundedEdgeRegularSubgraphs.SamplingHoeffding
public import BoundedEdgeRegularSubgraphs.MGFMoments
import Mathlib.Tactic

/-!
# The moments and both tails of sampling without replacement
-/

public section

open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [DecidableEq α]

/-- The sum of sampled values has mean `k * a` and variance at most `k/4`,
written as sums over the equally weighted samples. -/
theorem sample_deviation_moments (s : Finset α) (x : α → ℝ)
    (hs : 0 < s.card) (hx : ∀ i ∈ s, x i ∈ Set.Icc (0 : ℝ) 1) (k : ℕ) :
    let a := (∑ i ∈ s, x i) / (s.card : ℝ)
    let d (t : Finset α) := (∑ i ∈ t, x i) - (k : ℝ) * a
    (∑ t ∈ s.powersetCard k, d t) = 0 ∧
      (∑ t ∈ s.powersetCard k, d t ^ 2) ≤ (s.card.choose k : ℝ) * ((k : ℝ) / 4) := by
  intro a d
  have h (u : ℝ) : (∑ t ∈ s.powersetCard k, Real.exp (u * d t)) ≤
      ((s.powersetCard k).card : ℝ) * Real.exp (((k : ℝ) / 4) * u ^ 2 / 2) := by
    rw [Finset.card_powersetCard, show ((k : ℝ) / 4) * u ^ 2 / 2 = (k : ℝ) * u ^ 2 / 8 by ring]
    exact sum_exp_sample_deviation_le s x hs hx k u
  simpa only [Finset.card_powersetCard] using moments_of_sum_exp_le (s.powersetCard k) d h

private theorem card_sample_lower_deviation_le (s : Finset α) (x : α → ℝ)
    (hs : 0 < s.card) (hx : ∀ i ∈ s, x i ∈ Set.Icc (0 : ℝ) 1)
    (k : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    let a := (∑ i ∈ s, x i) / (s.card : ℝ)
    (((s.powersetCard k).filter fun t ↦ (k : ℝ) * ε ≤
      (k : ℝ) * a - (∑ i ∈ t, x i)).card : ℝ) ≤
        (s.card.choose k : ℝ) * Real.exp (-2 * (k : ℝ) * ε ^ 2) := by
  classical
  intro a
  let y (i : α) := 1 - x i
  have hy (i : α) (hi : i ∈ s) : y i ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨sub_nonneg.mpr (hx i hi).2, by dsimp [y]; linarith [(hx i hi).1]⟩
  have ha : (∑ i ∈ s, y i) / (s.card : ℝ) = 1 - a := by
    dsimp only [y, a]
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, sub_div,
      div_self (by positivity : (s.card : ℝ) ≠ 0)]
  have hu := card_sample_upper_deviation_le s y hs hy k hε
  dsimp only at hu
  rw [ha] at hu
  refine le_trans ?_ hu
  refine Nat.cast_le.mpr (Finset.card_le_card ?_)
  intro t ht
  obtain ⟨ht', hd⟩ := Finset.mem_filter.mp ht
  apply Finset.mem_filter.mpr
  refine ⟨ht', ?_⟩
  dsimp only [y]
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
    (Finset.mem_powersetCard.mp ht').2]
  linarith only [hd]

/-- The two-sided Hoeffding bound in Lemma 2.2, expressed as the number of
samples whose sum deviates by at least `k * ε` from its mean. -/
theorem card_sample_abs_deviation_le (s : Finset α) (x : α → ℝ)
    (hs : 0 < s.card) (hx : ∀ i ∈ s, x i ∈ Set.Icc (0 : ℝ) 1)
    (k : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    let a := (∑ i ∈ s, x i) / (s.card : ℝ)
    (((s.powersetCard k).filter fun t ↦ (k : ℝ) * ε ≤
      |(∑ i ∈ t, x i) - (k : ℝ) * a|).card : ℝ) ≤
        2 * (s.card.choose k : ℝ) * Real.exp (-2 * (k : ℝ) * ε ^ 2) := by
  classical
  intro a
  let U := s.powersetCard k
  let d (t : Finset α) := (∑ i ∈ t, x i) - (k : ℝ) * a
  let P := U.filter (fun t ↦ (k : ℝ) * ε ≤ d t)
  let N := U.filter (fun t ↦ (k : ℝ) * ε ≤ -d t)
  have hP : (P.card : ℝ) ≤ (s.card.choose k : ℝ) * Real.exp (-2 * (k : ℝ) * ε ^ 2) :=
    card_sample_upper_deviation_le s x hs hx k hε
  have hN : (N.card : ℝ) ≤ (s.card.choose k : ℝ) * Real.exp (-2 * (k : ℝ) * ε ^ 2) := by
    have hn := card_sample_lower_deviation_le s x hs hx k hε
    change _ ≤ _ at hn
    dsimp only [N, d, U]
    simpa only [neg_sub] using hn
  have hsub : U.filter (fun t ↦ (k : ℝ) * ε ≤ |d t|) ⊆ P ∪ N := by
    intro t ht
    obtain ⟨hU, hd⟩ := Finset.mem_filter.mp ht
    apply Finset.mem_union.mpr
    rcases le_total 0 (d t) with h | h
    · exact Or.inl (Finset.mem_filter.mpr ⟨hU, by simpa only [abs_of_nonneg h] using hd⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨hU, by simpa only [abs_of_nonpos h] using hd⟩)
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le P N)
  have hc' : ((U.filter (fun t ↦ (k : ℝ) * ε ≤ |d t|)).card : ℝ) ≤
      (P.card : ℝ) + (N.card : ℝ) := by exact_mod_cast hc
  linarith only [hc', hP, hN]

/-- The second moment and tail of a uniform sample, normalized by the number
of samples. The threshold `u` is an absolute deviation of the sum. -/
theorem uniform_sample_variance_and_tail (s : Finset α) (x : α → ℝ)
    (hx : ∀ i ∈ s, x i ∈ Set.Icc (0 : ℝ) 1)
    {k : ℕ} (hk₀ : 0 < k) (hk : k ≤ s.card) {u : ℝ} (hu : 0 ≤ u) :
    let a := (∑ i ∈ s, x i) / (s.card : ℝ)
    let d (t : Finset α) := (∑ i ∈ t, x i) - (k : ℝ) * a
    (∑ t ∈ s.powersetCard k, d t) / (s.card.choose k : ℝ) = 0 ∧
    (∑ t ∈ s.powersetCard k, d t ^ 2) / (s.card.choose k : ℝ) ≤ (k : ℝ) / 4 ∧
    (((s.powersetCard k).filter fun t ↦ u ≤ |d t|).card : ℝ) /
      (s.card.choose k : ℝ) ≤ 2 * Real.exp (-2 * u ^ 2 / k) := by
  classical
  intro a d
  have hs := hk₀.trans_le hk
  have hc : (0 : ℝ) < s.card.choose k := by exact_mod_cast Nat.choose_pos hk
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk₀
  obtain ⟨hm, hv⟩ := sample_deviation_moments s x hs hx k
  change (∑ t ∈ s.powersetCard k, d t) = 0 at hm
  change (∑ t ∈ s.powersetCard k, d t ^ 2) ≤ _ at hv
  refine ⟨by rw [hm, zero_div], (div_le_iff₀ hc).2 (by simpa only [mul_comm] using hv), ?_⟩
  have hh := card_sample_abs_deviation_le s x hs hx k (div_nonneg hu hkr.le)
  change (((s.powersetCard k).filter fun t ↦ (k : ℝ) * (u / k) ≤ |d t|).card : ℝ) ≤ _ at hh
  rw [show (k : ℝ) * (u / k) = u by field_simp] at hh
  rw [show -2 * (k : ℝ) * (u / k) ^ 2 = -2 * u ^ 2 / k by field_simp] at hh
  exact (div_le_iff₀ hc).2 (by simpa only [mul_right_comm] using hh)

end BoundedEdgeRegularSubgraphs
