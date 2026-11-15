/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Pointwise
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Half-open cells and their exact translated overlap

The product is exactly the indicator of the intersection interval. Thus the
half-open convention causes no exceptional-set assumption in the pairwise
correlation identity used by the discrete partition bridge.
-/

namespace ErdosOverlap.Discrete

open MeasureTheory Set

public section

@[expose] noncomputable def intervalCell (δ a : ℝ) : ℝ → ℝ :=
  (Ico a (a + δ)).indicator (fun _ => (1 : ℝ))

theorem intervalCell_measurable (δ a : ℝ) : Measurable (intervalCell δ a) :=
  measurable_const.indicator measurableSet_Ico

theorem intervalCell_integrable (δ a : ℝ) : Integrable (intervalCell δ a) := by
  apply IntegrableOn.integrable_indicator _ measurableSet_Ico
  exact integrableOn_const measure_Ico_lt_top.ne

theorem intervalCell_nonneg (δ a x : ℝ) : 0 ≤ intervalCell δ a x := by
  by_cases hx : x ∈ Ico a (a + δ) <;> simp [intervalCell, hx]

theorem intervalCell_le_one (δ a x : ℝ) : intervalCell δ a x ≤ 1 := by
  by_cases hx : x ∈ Ico a (a + δ) <;> simp [intervalCell, hx]

theorem integral_intervalCell_max (δ a : ℝ) :
    (∫ x : ℝ, intervalCell δ a x) = max δ 0 := by
  rw [intervalCell, integral_indicator_const (1 : ℝ) measurableSet_Ico,
    smul_eq_mul, mul_one, Real.volume_real_Ico]
  congr 1
  ring

theorem integral_intervalCell (δ a : ℝ) (hδ : 0 ≤ δ) :
    (∫ x : ℝ, intervalCell δ a x) = δ := by
  rw [integral_intervalCell_max, max_eq_left hδ]

theorem intervalCell_product_eq_indicator (δ a b t : ℝ) :
    (fun x => intervalCell δ a x * intervalCell δ b (x + t)) =
      (Ico (max a (b - t)) (min (a + δ) (b + δ - t))).indicator
        (fun _ => (1 : ℝ)) := by
  funext x
  by_cases hx : x ∈ Ico a (a + δ)
  · by_cases hxt : x + t ∈ Ico b (b + δ)
    · have hboth : x ∈ Ico (max a (b - t)) (min (a + δ) (b + δ - t)) :=
        ⟨max_le hx.1 (by linarith [hxt.1]), lt_min hx.2 (by linarith [hxt.2])⟩
      simp [intervalCell, hx, hxt, hboth]
    · have hnot : x ∉ Ico (max a (b - t)) (min (a + δ) (b + δ - t)) := by
        intro hboth
        exact hxt ⟨by linarith [(max_le_iff.mp hboth.1).2],
          by linarith [(lt_min_iff.mp hboth.2).2]⟩
      simp [intervalCell, hx, hxt, hnot]
  · have hnot : x ∉ Ico (max a (b - t)) (min (a + δ) (b + δ - t)) := by
      intro hboth
      exact hx ⟨(max_le_iff.mp hboth.1).1, (lt_min_iff.mp hboth.2).1⟩
    simp [intervalCell, hx, hnot]

theorem intervalCell_product_integrable (δ a b t : ℝ) :
    Integrable (fun x => intervalCell δ a x * intervalCell δ b (x + t)) := by
  rw [intervalCell_product_eq_indicator]
  apply IntegrableOn.integrable_indicator _ measurableSet_Ico
  exact integrableOn_const measure_Ico_lt_top.ne

theorem intervalCell_correlation (δ a b t : ℝ) :
    (∫ x : ℝ, intervalCell δ a x * intervalCell δ b (x + t)) =
      max (δ - |t - (b - a)|) 0 := by
  rw [intervalCell_product_eq_indicator,
    integral_indicator_const (1 : ℝ) measurableSet_Ico,
    smul_eq_mul, mul_one, Real.volume_real_Ico]
  rcases le_total 0 (t - (b - a)) with ht | ht
  · rw [abs_of_nonneg ht, max_eq_left (by linarith : b - t ≤ a),
      min_eq_right (by linarith : b + δ - t ≤ a + δ)]
    congr 1
    ring
  · rw [abs_of_nonpos ht, max_eq_right (by linarith : a ≤ b - t),
      min_eq_left (by linarith : a + δ ≤ b + δ - t)]
    congr 1
    ring

end
end ErdosOverlap.Discrete
