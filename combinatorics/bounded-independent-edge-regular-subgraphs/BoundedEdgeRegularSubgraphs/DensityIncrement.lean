module

public import BoundedEdgeRegularSubgraphs.BernoulliLowerTail
public import BoundedEdgeRegularSubgraphs.DensitySurplus
import BoundedEdgeRegularSubgraphs.Induce
import BoundedEdgeRegularSubgraphs.MeanDrift
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic

/-!
# Density increment by independent vertex selection
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BoundedEdgeRegularSubgraphs

variable {α : Type*} [Fintype α] [LinearOrder α]

private theorem vertexSelectionWeight_mem_Icc (q : Edge α → Set.Icc (0 : ℝ) 1)
    (hn : 2 ≤ Fintype.card α) (i : α) : vertexSelectionWeight q i ∈ Set.Icc 0 1 := by
  let n : ℝ := Fintype.card α
  let μ := degreeSum fun e ↦ (q e : ℝ)
  have hn' : 2 ≤ n := by dsimp only [n]; exact_mod_cast hn
  have hn₀ : 0 < n := by linarith
  have hd (i : α) : μ i ∈ Set.Icc 0 (n - 1) := degreeSum_probability_bounds q i
  have hmean₀ : 0 ≤ vertexMean μ :=
    div_nonneg (Finset.sum_nonneg fun j _ ↦ (hd j).1) hn₀.le
  have hmean₁ : vertexMean μ ≤ n - 1 := by
    apply (div_le_iff₀ hn₀).2
    have hs := Finset.sum_le_sum (s := (Finset.univ : Finset α)) (fun j _ ↦ (hd j).2)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
    simpa only [mul_comm (n - 1) n] using hs
  have hl : (-1 : ℝ) ≤ (μ i - vertexMean μ) / n := by
    apply (le_div_iff₀ hn₀).2
    linarith only [(hd i).1, hmean₁]
  have hu : (μ i - vertexMean μ) / n ≤ 1 := by
    apply (div_le_iff₀ hn₀).2
    linarith only [(hd i).2, hmean₀]
  change 0 ≤ 1 / 2 + (μ i - vertexMean μ) / n / 4 ∧
    1 / 2 + (μ i - vertexMean μ) / n / 4 ≤ 1
  constructor <;> linarith only [hl, hu]

private theorem sum_vertexSelectionWeight (q : Edge α → Set.Icc (0 : ℝ) 1) :
    (∑ i, vertexSelectionWeight q i) = (Fintype.card α : ℝ) / 2 := by
  simp only [vertexSelectionWeight, Finset.sum_add_distrib, ← Finset.sum_div,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, sum_sub_vertexMean, zero_div, add_zero]
  ring

omit [Fintype α] [LinearOrder α] in
private theorem measurable_selectionCoord (i : α) :
    Measurable (fun x : α → ℝ ↦ selectionIndicator (x i)) :=
  measurable_selectionIndicator.comp (measurable_pi_apply i)

private theorem integral_selection_pair (w : α → Set.Icc (0 : ℝ) 1)
    (e : Edge α) :
    (∫ x, selectionIndicator (x e.val.1) * selectionIndicator (x e.val.2)
      ∂bernoulliProduct w) = (w e.val.1 : ℝ) * (w e.val.2 : ℝ) := by
  have hind : iIndepFun (fun i (x : α → ℝ) ↦ selectionIndicator (x i)) (bernoulliProduct w) :=
    iIndepFun_pi (X := fun _ ↦ selectionIndicator) (fun _ ↦ measurable_selectionIndicator.aemeasurable)
  have hm (i : α) :
      (∫ x, selectionIndicator (x i) ∂bernoulliProduct w) = (w i : ℝ) := by
    have hp := measurePreserving_eval (fun j ↦ bernoulliMeasure (1 : ℝ) 0 (w j)) i
    calc
      _ = ∫ x, selectionIndicator x ∂bernoulliMeasure (1 : ℝ) 0 (w i) := by
        rw [← hp.map_eq, integral_map hp.measurable.aemeasurable
          measurable_selectionIndicator.aestronglyMeasurable]
        rfl
      _ = _ := by rw [integral_bernoulliMeasure]; simp [selectionIndicator]
  rw [(hind.indepFun e.property.ne).integral_fun_mul_eq_mul_integral
    (measurable_selectionCoord _).aestronglyMeasurable
    (measurable_selectionCoord _).aestronglyMeasurable, hm, hm]

private noncomputable def selectedVertices (x : α → ℝ) : Finset α :=
  Finset.univ.filter fun i ↦ x i = 1

omit [LinearOrder α] in
private theorem selectedVertices_card (x : α → ℝ) :
    ((selectedVertices x).card : ℝ) = selectionSize x := by
  rw [selectedVertices, Finset.card_filter]
  push_cast
  simp [selectionSize, selectionIndicator]

private theorem surplus_eq_induced_sum (q : Edge α → Set.Icc (0 : ℝ) 1)
    (g : ℝ) (x : α → ℝ) :
    (∑ e : Edge α, ((q e : ℝ) - g) *
      (selectionIndicator (x e.val.1) * selectionIndicator (x e.val.2))) =
        ∑ e : Edge ↥(selectedVertices x), ((q (inducedEdge (selectedVertices x) e) : ℝ) - g) := by
  classical
  let S := selectedVertices x
  have h (e : Edge α) : ((q e : ℝ) - g) *
      (selectionIndicator (x e.val.1) * selectionIndicator (x e.val.2)) =
        if e.val.1 ∈ S ∧ e.val.2 ∈ S then (q e : ℝ) - g else 0 := by
    simp only [S, selectedVertices, Finset.mem_filter, Finset.mem_univ, true_and, selectionIndicator]
    split_ifs <;> simp_all
  simp_rw [h, ← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun e _ ↦ inducedEdge S e) ?_ ?_ ?_ ?_
  · intro e _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.val.1.property, e.val.2.property⟩
  · intro e _ f _ h
    exact inducedEdge_injective S h
  · intro e he
    obtain ⟨h₁, h₂⟩ := (Finset.mem_filter.mp he).2
    exact ⟨⟨(⟨e.val.1, h₁⟩, ⟨e.val.2, h₂⟩), e.property⟩, Finset.mem_univ _, Subtype.ext rfl⟩
  · intros
    rfl

/-- Lemma 5.1. A normalized degree variance above the exponential threshold
gives a set of at least a quarter of the vertices with increased density. -/
theorem exists_density_increment (q : Edge α → Set.Icc (0 : ℝ) 1)
    (hn : 32 ≤ Fintype.card α)
    (hv : 16 * Real.exp (-(Fintype.card α : ℝ) / 8) < normalizedDegreeVariation q) :
    ∃ S : Finset α, Fintype.card α ≤ 4 * S.card ∧
      arrayDensity q + normalizedDegreeVariation q / 2 < arrayDensity (induce S q) := by
  classical
  let n : ℝ := Fintype.card α
  let v := normalizedDegreeVariation q
  let g := arrayDensity q + v / 2
  let w (i : α) : Set.Icc (0 : ℝ) 1 :=
    ⟨vertexSelectionWeight q i, vertexSelectionWeight_mem_Icc q (by omega) i⟩
  let μ := bernoulliProduct w
  let B : Set (α → ℝ) := {x | selectionSize x < n / 4}
  let f (e : Edge α) (x : α → ℝ) :=
    ((q e : ℝ) - g) * (selectionIndicator (x e.val.1) * selectionIndicator (x e.val.2))
  let F (x : α → ℝ) := ∑ e : Edge α, f e x
  have hn' : (32 : ℝ) ≤ n := by dsimp only [n]; exact_mod_cast hn
  have hn₀ : 0 < n := by linarith
  have hg : 0 ≤ g := by
    have hv₀ : 0 ≤ v := (mul_nonneg (by norm_num) (Real.exp_nonneg _)).trans hv.le
    dsimp only [g, arrayDensity]
    exact add_nonneg (div_nonneg
      (mul_nonneg (by norm_num) (Finset.sum_nonneg fun e _ ↦ (q e).property.1))
      (mul_nonneg hn₀.le (by linarith))) (by positivity)
  have hfi (e : Edge α) : Integrable (f e) μ := by
    refine Integrable.of_bound (measurable_const.mul
      ((measurable_selectionCoord _).mul (measurable_selectionCoord _))).aestronglyMeasurable
      |(q e : ℝ) - g| (Filter.Eventually.of_forall fun x ↦ ?_)
    dsimp only [f]
    rw [Real.norm_eq_abs, abs_mul]
    have h₁ := selectionIndicator_mem_Icc (x e.val.1)
    have h₂ := selectionIndicator_mem_Icc (x e.val.2)
    rw [abs_of_nonneg (mul_nonneg h₁.1 h₂.1)]
    exact mul_le_of_le_one_right (abs_nonneg _) ((mul_le_of_le_one_left h₂.1 h₁.2).trans h₂.2)
  have hF : Integrable F μ := integrable_finsetSum _ (fun e _ ↦ hfi e)
  have hexpect : n ^ 2 * v / 32 ≤ ∫ x, F x ∂μ := by
    change _ ≤ ∫ x, ∑ e : Edge α, f e x ∂μ
    rw [integral_finsetSum _ (fun e _ ↦ hfi e)]
    have he (e : Edge α) : (∫ x, f e x ∂μ) =
        ((q e : ℝ) - g) * ((w e.val.1 : ℝ) * (w e.val.2 : ℝ)) := by
      change (∫ x, ((q e : ℝ) - g) * (selectionIndicator (x e.val.1) *
        selectionIndicator (x e.val.2)) ∂bernoulliProduct w) = _
      rw [integral_const_mul, integral_selection_pair]
    simp_rw [he]
    exact density_increment_weighted_surplus q (by omega)
  have hB : MeasurableSet B := measurableSet_lt measurable_selectionSize measurable_const
  have hBprob : μ.real B ≤ Real.exp (-n / 8) :=
    probability_selectionSize_lt_quarter w (sum_vertexSelectionWeight q)
  by_contra! hnone
  have hpoint (x : α → ℝ) : F x ≤ B.indicator (fun _ ↦ n ^ 2 / 2) x := by
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx]
      have he (e : Edge α) : f e x ≤ 1 := by
        have h₁ := selectionIndicator_mem_Icc (x e.val.1)
        have h₂ := selectionIndicator_mem_Icc (x e.val.2)
        exact (mul_le_of_le_one_left (mul_nonneg h₁.1 h₂.1)
          ((sub_le_self _ hg).trans (q e).property.2)).trans
            ((mul_le_of_le_one_left h₂.1 h₁.2).trans h₂.2)
      have ht := Finset.sum_le_sum (s := (Finset.univ : Finset (Edge α))) (fun e _ ↦ he e)
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at ht
      have hc := card_edge_twice (α := α)
      change 2 * (Fintype.card (Edge α) : ℝ) = n * (n - 1) at hc
      change F x ≤ _ at ht
      nlinarith only [hc, ht, hn₀.le]
    · rw [Set.indicator_of_notMem hx]
      let S := selectedVertices x
      have ha : n / 4 ≤ (S.card : ℝ) := by
        rw [selectedVertices_card]
        exact le_of_not_gt hx
      have hcard : Fintype.card α ≤ 4 * S.card := by
        have hh : n ≤ 4 * (S.card : ℝ) := by linarith only [ha]
        dsimp only [n] at hh
        exact_mod_cast hh
      have hd := hnone S hcard
      have hden : 0 < (Fintype.card ↥S : ℝ) * ((Fintype.card ↥S : ℝ) - 1) := by
        rw [Fintype.card_coe]
        apply mul_pos <;> linarith only [ha, hn']
      change 2 * (∑ e : Edge ↥S, (q (inducedEdge S e) : ℝ)) /
        ((Fintype.card ↥S : ℝ) * ((Fintype.card ↥S : ℝ) - 1)) ≤ g at hd
      have hh := (div_le_iff₀ hden).1 hd
      have hc := card_edge_twice (α := ↥S)
      rw [← hc] at hh
      change (∑ e : Edge α, ((q e : ℝ) - g) *
        (selectionIndicator (x e.val.1) * selectionIndicator (x e.val.2))) ≤ 0
      rw [surplus_eq_induced_sum, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      linarith only [hh]
  have htop := integral_mono hF ((integrable_const (n ^ 2 / 2)).indicator hB) hpoint
  rw [integral_indicator_const _ hB, smul_eq_mul] at htop
  have hfinal := hexpect.trans (htop.trans (mul_le_mul_of_nonneg_right hBprob (by positivity)))
  have hstrict := mul_lt_mul_of_pos_left hv (show 0 < n ^ 2 by positivity)
  nlinarith only [hfinal, hstrict]

end BoundedEdgeRegularSubgraphs
