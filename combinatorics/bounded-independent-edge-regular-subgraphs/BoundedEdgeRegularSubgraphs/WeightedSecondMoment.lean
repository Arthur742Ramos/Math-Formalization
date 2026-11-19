module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-!
# The inverse-probability weighted second moment
-/

public section

open MeasureTheory
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {ι Ω : Type*} [MeasurableSpace Ω]

@[expose] noncomputable def weightedEventCount (μ : Measure Ω) (S : Finset ι)
    (E : ι → Set Ω) (x : Ω) : ℝ :=
  ∑ i ∈ S, (E i).indicator (fun _ ↦ (μ.real (E i))⁻¹) x

/-- The first and second moments of the inverse-probability weighted count. -/
theorem weightedEventCount_moments (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Finset ι) (E : ι → Set Ω) (hE : ∀ i ∈ S, MeasurableSet (E i))
    (hp : ∀ i ∈ S, 0 < μ.real (E i)) :
    let Z := weightedEventCount μ S E
    Integrable Z μ ∧ Integrable (fun x ↦ Z x ^ 2) μ ∧
      (∫ x, Z x ∂μ) = (S.card : ℝ) ∧
      (∫ x, Z x ^ 2 ∂μ) = ∑ i ∈ S, ∑ j ∈ S, μ.real (E i ∩ E j) /
        (μ.real (E i) * μ.real (E j)) := by
  classical
  let m : ℝ := S.card
  let p (i : ι) := μ.real (E i)
  let f (i : ι) : Ω → ℝ := (E i).indicator fun _ ↦ (p i)⁻¹
  intro Z
  have hfi (i : ι) (hi : i ∈ S) : Integrable (f i) μ :=
    (integrable_const _).indicator (hE i hi)
  have hZ : Integrable Z μ := integrable_finsetSum _ hfi
  have hmul (i j : ι) (x : Ω) : f i x * f j x =
      (E i ∩ E j).indicator (fun _ ↦ (p i * p j)⁻¹) x := by
    by_cases hi : x ∈ E i <;> by_cases hj : x ∈ E j <;>
      simp [f, hi, hj, mul_comm]
  have hfi2 (i : ι) (hi : i ∈ S) (j : ι) (hj : j ∈ S) :
      Integrable (fun x ↦ f i x * f j x) μ := by
    simp_rw [hmul]
    exact (integrable_const _).indicator ((hE i hi).inter (hE j hj))
  have hZeq (x : Ω) : Z x ^ 2 = ∑ i ∈ S, ∑ j ∈ S, f i x * f j x := by
    change (∑ i ∈ S, f i x) ^ 2 = _
    rw [pow_two, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  have hZ2 : Integrable (fun x ↦ Z x ^ 2) μ := by
    simp_rw [hZeq]
    exact integrable_finsetSum _ (fun i hi ↦ integrable_finsetSum _ (hfi2 i hi))
  have hmean : (∫ x, Z x ∂μ) = m := by
    change (∫ x, ∑ i ∈ S, f i x ∂μ) = _
    rw [integral_finsetSum _ hfi]
    calc
      _ = ∑ _ ∈ S, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        change (∫ x, (E i).indicator (fun _ ↦ (p i)⁻¹) x ∂μ) = 1
        rw [integral_indicator_const _ (hE i hi), smul_eq_mul]
        exact mul_inv_cancel₀ (hp i hi).ne'
      _ = _ := by simp [m]
  have hsecond : (∫ x, Z x ^ 2 ∂μ) =
      ∑ i ∈ S, ∑ j ∈ S, μ.real (E i ∩ E j) / (p i * p j) := by
    simp_rw [hZeq]
    rw [integral_finsetSum _ (fun i hi ↦ integrable_finsetSum _ (hfi2 i hi))]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum _ (hfi2 i hi)]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [hmul, integral_indicator_const _ ((hE i hi).inter (hE j hj)),
      smul_eq_mul, div_eq_mul_inv]
  exact ⟨hZ, hZ2, hmean, hsecond⟩

/-- The failure probability for a finite family of events, using each
indicator weighted by the inverse of its own probability. -/
theorem probability_no_event_le_weighted_second_moment (μ : Measure Ω)
    [IsProbabilityMeasure μ] (S : Finset ι) (hS : S.Nonempty)
    (E : ι → Set Ω) (hE : ∀ i ∈ S, MeasurableSet (E i))
    (hp : ∀ i ∈ S, 0 < μ.real (E i)) :
    μ.real (⋂ i ∈ S, (E i)ᶜ) ≤
      ((∑ i ∈ S, ∑ j ∈ S, μ.real (E i ∩ E j) /
        (μ.real (E i) * μ.real (E j))) - (S.card : ℝ) ^ 2) / (S.card : ℝ) ^ 2 := by
  classical
  let B := ⋂ i ∈ S, (E i)ᶜ
  let m : ℝ := S.card
  let p (i : ι) := μ.real (E i)
  let f (i : ι) : Ω → ℝ := (E i).indicator fun _ ↦ (p i)⁻¹
  let Z := weightedEventCount μ S E
  have hm : 0 < m := Nat.cast_pos.mpr hS.card_pos
  have hB : MeasurableSet B := S.measurableSet_biInter (fun i hi ↦ (hE i hi).compl)
  obtain ⟨hZ, hZ2, hmean, hsecond⟩ := weightedEventCount_moments μ S E hE hp
  have hD (x : Ω) : (Z x - m) ^ 2 = Z x ^ 2 - (2 * m) * Z x + m ^ 2 := by ring
  have hiD : Integrable (fun x ↦ (Z x - m) ^ 2) μ := by
    simp_rw [hD]
    exact (hZ2.sub (hZ.const_mul _)).add (integrable_const _)
  have heD : (∫ x, (Z x - m) ^ 2 ∂μ) =
      (∑ i ∈ S, ∑ j ∈ S, μ.real (E i ∩ E j) / (p i * p j)) - m ^ 2 := by
    simp_rw [hD]
    have hiMul : Integrable (fun x ↦ (2 * m) * Z x) μ := hZ.const_mul _
    have hiSub : Integrable (fun x ↦ Z x ^ 2 - (2 * m) * Z x) μ := hZ2.sub hiMul
    rw [integral_add hiSub (integrable_const _), integral_sub hZ2 hiMul,
      integral_const_mul, integral_const,
      hmean, hsecond, probReal_univ, one_smul]
    ring
  have hbound (x : Ω) : B.indicator (fun _ ↦ m ^ 2) x ≤ (Z x - m) ^ 2 := by
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx]
      have hzero : Z x = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hnot : x ∉ E i := by
          have hall : ∀ i ∈ S, x ∉ E i := by
            simpa only [B, Set.mem_iInter, Set.mem_compl_iff] using hx
          exact hall i hi
        exact Set.indicator_of_notMem (f := fun _ ↦ (p i)⁻¹) hnot
      rw [hzero, zero_sub, neg_sq]
    · rw [Set.indicator_of_notMem hx]
      exact sq_nonneg _
  have h := integral_mono ((integrable_const (m ^ 2)).indicator hB) hiD hbound
  rw [integral_indicator_const _ hB, smul_eq_mul, heD] at h
  exact (le_div_iff₀ (sq_pos_of_pos hm)).2 h

end BoundedEdgeRegularSubgraphs
