module

public import BoundedEdgeRegularSubgraphs.WeightedSecondMoment
import Mathlib.Tactic

/-!
# Positive probability from a supported second moment
-/

public section

open MeasureTheory Set

namespace BoundedEdgeRegularSubgraphs

/-- Cauchy–Schwarz in the form used for the positive-probability
deduction from an indicator-weighted count. -/
theorem sq_integral_le_measure_mul_integral_sq_of_zero_off
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (A : Set Ω) (hA : MeasurableSet A) (f : Ω → ℝ)
    (hf : Integrable f μ) (hf₂ : Integrable (fun x ↦ f x ^ 2) μ)
    (hZero : ∀ x ∉ A, f x = 0) :
    (∫ x, f x ∂μ) ^ 2 ≤ μ.real A * ∫ x, f x ^ 2 ∂μ := by
  let c := ∫ x, f x ∂μ
  let t := μ.real A
  let g (x : Ω) := (t * f x - A.indicator (fun _ ↦ c) x) ^ 2
  have he : A.indicator f = f := by
    funext x
    by_cases hx : x ∈ A
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, hZero x hx]
  rcases (measureReal_nonneg (μ := μ) (s := A)).eq_or_lt with ht | ht
  · have hz : μ A = 0 := by
      have h := ENNReal.ofReal_toReal (measure_ne_top μ A)
      change ENNReal.ofReal (μ.real A) = μ A at h
      rw [← ht, ENNReal.ofReal_zero] at h
      exact h.symm
    have hc : c = 0 := by
      change (∫ x, f x ∂μ) = 0
      rw [← he, integral_indicator hA, Measure.restrict_eq_zero.mpr hz, integral_zero_measure]
    change c ^ 2 ≤ t * ∫ x, f x ^ 2 ∂μ
    rw [hc, show t = 0 from ht.symm, zero_mul]
    norm_num
  have hg (x : Ω) : g x = t ^ 2 * f x ^ 2 - (2 * t * c) * f x +
      A.indicator (fun _ ↦ c ^ 2) x := by
    by_cases hx : x ∈ A
    · unfold g
      rw [indicator_of_mem hx, indicator_of_mem hx]
      ring
    · unfold g
      rw [indicator_of_notMem hx, indicator_of_notMem hx, hZero x hx]
      ring
  have hi₁ : Integrable (fun x ↦ t ^ 2 * f x ^ 2) μ := hf₂.const_mul _
  have hi₂ : Integrable (fun x ↦ (2 * t * c) * f x) μ := hf.const_mul _
  have hi₃ : Integrable (A.indicator (fun _ ↦ c ^ 2)) μ := (integrable_const _).indicator hA
  have hi₄ : Integrable (fun x ↦ t ^ 2 * f x ^ 2 - (2 * t * c) * f x) μ := hi₁.sub hi₂
  have hn := integral_nonneg (μ := μ) (f := g) (fun x ↦ sq_nonneg _)
  simp_rw [hg] at hn
  rw [integral_add hi₄ hi₃, integral_sub hi₁ hi₂, integral_const_mul, integral_const_mul,
    integral_indicator_const _ hA, smul_eq_mul] at hn
  change 0 ≤ t ^ 2 * (∫ x, f x ^ 2 ∂μ) - (2 * t * c) * c + t * c ^ 2 at hn
  apply (le_of_mul_le_mul_left (a := t)) _ ht
  change t * c ^ 2 ≤ t * (t * ∫ x, f x ^ 2 ∂μ)
  nlinarith only [hn]

/-- A uniform bound on the normalized second moment gives its reciprocal
as a lower bound for the probability of at least one event. -/
theorem probability_event_union_ge_of_weighted_second_moment_bound
    {ι Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Finset ι) (hS : S.Nonempty) (E : ι → Set Ω)
    (hE : ∀ i ∈ S, MeasurableSet (E i)) (hp : ∀ i ∈ S, 0 < μ.real (E i))
    {K : ℝ} (hK : 0 < K)
    (hb : (∑ i ∈ S, ∑ j ∈ S, μ.real (E i ∩ E j) / (μ.real (E i) * μ.real (E j))) ≤
      K * (S.card : ℝ) ^ 2) :
    K⁻¹ ≤ μ.real (⋃ i ∈ S, E i) := by
  let A := ⋃ i ∈ S, E i
  let Z := weightedEventCount μ S E
  have hA : MeasurableSet A := S.measurableSet_biUnion hE
  obtain ⟨hZ, hZ₂, hMean, hSecond⟩ := weightedEventCount_moments μ S E hE hp
  have hZero (x : Ω) (hx : x ∉ A) : Z x = 0 := by
    unfold Z weightedEventCount
    apply Finset.sum_eq_zero
    intro i hi
    apply indicator_of_notMem
    intro he
    exact hx (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, he⟩⟩)
  have h := sq_integral_le_measure_mul_integral_sq_of_zero_off μ A hA Z hZ hZ₂ hZero
  change (∫ x, weightedEventCount μ S E x ∂μ) ^ 2 ≤ μ.real A *
    ∫ x, weightedEventCount μ S E x ^ 2 ∂μ at h
  rw [hMean, hSecond] at h
  have hh := h.trans (mul_le_mul_of_nonneg_left hb (measureReal_nonneg (μ := μ)))
  rw [← mul_assoc] at hh
  have hs : 0 < (S.card : ℝ) ^ 2 := sq_pos_of_pos (Nat.cast_pos.mpr hS.card_pos)
  exact (inv_le_iff_one_le_mul₀ hK).2 (by
    exact le_of_mul_le_mul_right (by simpa only [one_mul] using hh) hs)

end BoundedEdgeRegularSubgraphs
