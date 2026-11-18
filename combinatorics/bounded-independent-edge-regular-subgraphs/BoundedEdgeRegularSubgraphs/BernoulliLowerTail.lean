module

public import BoundedEdgeRegularSubgraphs.ScalarAtoms
import BoundedEdgeRegularSubgraphs.Tilt
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

/-!
# A lower-tail bound for a Bernoulli sample
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {ι : Type*} [Fintype ι]

/-- Indicator of a selected vertex in a Bernoulli product outcome. -/
noncomputable def selectionIndicator (x : ℝ) : ℝ :=
  if x = 1 then 1 else 0

theorem measurable_selectionIndicator : Measurable selectionIndicator :=
  Measurable.ite (measurableSet_singleton (1 : ℝ)) measurable_one measurable_zero

theorem selectionIndicator_mem_Icc (x : ℝ) : selectionIndicator x ∈ Set.Icc (0 : ℝ) 1 := by
  unfold selectionIndicator
  split <;> norm_num

/-- Real-valued size of the selected set. -/
noncomputable def selectionSize (x : ι → ℝ) : ℝ := ∑ i, selectionIndicator (x i)

theorem measurable_selectionSize : Measurable (selectionSize (ι := ι)) :=
  Finset.measurable_sum _ (fun i _ ↦ measurable_selectionIndicator.comp (measurable_pi_apply i))

theorem selectionSize_nonneg (x : ι → ℝ) : 0 ≤ selectionSize x :=
  Finset.sum_nonneg (fun i _ ↦ (selectionIndicator_mem_Icc (x i)).1)

theorem selectionSize_le_card (x : ι → ℝ) : selectionSize x ≤ Fintype.card ι := by
  unfold selectionSize
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using
    Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ (selectionIndicator_mem_Icc (x i)).2)

/-- The product moment bound for independent Bernoulli selections. -/
theorem integral_exp_selectionSize_le (q : ι → Set.Icc (0 : ℝ) 1) (u : ℝ) :
    (∫ x, Real.exp (u * (selectionSize x - ∑ i, (q i : ℝ))) ∂bernoulliProduct q) ≤
      Real.exp ((Fintype.card ι : ℝ) * u ^ 2 / 8) := by
  let f (i : ι) (x : ℝ) := Real.exp (u * (selectionIndicator x - (q i : ℝ)))
  have hexp (x : ι → ℝ) : Real.exp (u * (selectionSize x - ∑ i, (q i : ℝ))) =
      ∏ i, f i (x i) := by
    dsimp only [f, selectionSize]
    rw [← Real.exp_sum, ← Finset.mul_sum, Finset.sum_sub_distrib]
  simp_rw [hexp]
  unfold bernoulliProduct
  rw [integral_fintype_prod_eq_prod f, show (Fintype.card ι : ℝ) * u ^ 2 / 8 =
    (Fintype.card ι : ℝ) * (u ^ 2 / 8) by ring, Real.exp_nat_mul, ← Finset.card_univ (α := ι),
    ← Finset.prod_const]
  have hf (i : ι) : (∫ x, f i x ∂bernoulliMeasure (1 : ℝ) 0 (q i)) =
      Real.exp (Real.log (tiltNormalizer (q i) u) - (q i : ℝ) * u) := by
    rw [integral_bernoulliMeasure]
    simp only [f, selectionIndicator, ite_true, zero_ne_one, ite_false, smul_eq_mul,
      sub_eq_add_neg ((Real.log (tiltNormalizer (q i) u))),
      Real.exp_add, Real.exp_log (tiltNormalizer_pos _ _)]
    rw [show u * (1 - (q i : ℝ)) = u + -((q i : ℝ) * u) by ring,
      show u * (0 - (q i : ℝ)) = -((q i : ℝ) * u) by ring, Real.exp_add]
    unfold tiltNormalizer
    ring
  simp_rw [hf]
  exact Finset.prod_le_prod₀ (fun _ _ ↦ Real.exp_nonneg _)
    (fun i _ ↦ Real.exp_le_exp.mpr (logTiltNormalizer_sub_le (q i) u))

/-- A Bernoulli sample of mean half the population has an exponentially
small probability of selecting fewer than one quarter of the vertices. -/
theorem probability_selectionSize_lt_quarter (q : ι → Set.Icc (0 : ℝ) 1)
    (hq : (∑ i, (q i : ℝ)) = (Fintype.card ι : ℝ) / 2) :
    (bernoulliProduct q).real {x | selectionSize x < (Fintype.card ι : ℝ) / 4} ≤
      Real.exp (-(Fintype.card ι : ℝ) / 8) := by
  let n : ℝ := Fintype.card ι
  let B : Set (ι → ℝ) := {x | selectionSize x < n / 4}
  let F (x : ι → ℝ) := Real.exp (n / 2 - selectionSize x)
  let g : (ι → ℝ) → ℝ := B.indicator fun _ ↦ Real.exp (n / 4)
  have hB : MeasurableSet B := measurableSet_lt measurable_selectionSize measurable_const
  have hF : Integrable F (bernoulliProduct q) := by
    refine Integrable.of_bound (Real.continuous_exp.measurable.comp
      (measurable_const.sub measurable_selectionSize)).aestronglyMeasurable
      (Real.exp (n / 2)) (Filter.Eventually.of_forall fun x ↦ ?_)
    dsimp only [F]
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_exp.mpr (sub_le_self _ (selectionSize_nonneg x))
  have hg : Integrable g (bernoulliProduct q) := (integrable_const _).indicator hB
  have hpoint (x : ι → ℝ) : g x ≤ F x := by
    by_cases hx : x ∈ B
    · dsimp only [g]
      rw [Set.indicator_of_mem hx]
      apply Real.exp_le_exp.mpr
      change selectionSize x < n / 4 at hx
      linarith
    · dsimp only [g]
      rw [Set.indicator_of_notMem hx]
      exact Real.exp_nonneg _
  have hupper := integral_exp_selectionSize_le q (-1)
  rw [hq] at hupper
  change (∫ x, Real.exp ((-1 : ℝ) * (selectionSize x - n / 2)) ∂bernoulliProduct q) ≤
    Real.exp (n * (-1 : ℝ) ^ 2 / 8) at hupper
  simp only [neg_one_mul, neg_sub, neg_sq, one_pow, mul_one] at hupper
  have h := (integral_mono hg hF hpoint).trans hupper
  change (∫ x, B.indicator (fun _ ↦ Real.exp (n / 4)) x ∂bernoulliProduct q) ≤ _ at h
  rw [integral_indicator_const _ hB, smul_eq_mul] at h
  have hh := (le_div_iff₀ (Real.exp_pos (n / 4))).2 h
  rw [← Real.exp_sub, show n / 8 - n / 4 = -n / 8 by ring] at hh
  exact hh

end BoundedEdgeRegularSubgraphs
