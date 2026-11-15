/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Constant
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The physical first moment under an overlap cap

The odd profile satisfies `|d(t)| ≤ min t H` on `[0,1]`. Integrating this
physical estimate gives `|m| ≤ 2 H - H²` for any overlap cap `0 ≤ H ≤ 1`.
Consequently a mean interval above this threshold is impossible under the
tested cap, and its physical row inequality needs no kernel computation.
-/

@[expose] public section

namespace ErdosOverlap

open MeasureTheory Set
open scoped Interval

noncomputable section

theorem integral_min_id_const {H : ℝ} (hH0 : 0 ≤ H) (hH1 : H ≤ 1) :
    (∫ t in (0 : ℝ)..1, min t H) = H - H^2/2 := by
  have hc : Continuous (fun t : ℝ => min t H) := continuous_id.min continuous_const
  have hleft : (∫ t in (0 : ℝ)..H, min t H) = H^2/2 := by
    calc
      (∫ t in (0 : ℝ)..H, min t H) = ∫ t in (0 : ℝ)..H, t := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hH0] at ht
        exact min_eq_left ht.2
      _ = H^2/2 := by simp
  have hright : (∫ t in H..(1 : ℝ), min t H) = (1-H)*H := by
    calc
      (∫ t in H..(1 : ℝ), min t H) = ∫ _t in H..(1 : ℝ), H := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hH1] at ht
        exact min_eq_right ht.1
      _ = (1-H)*H := by simp
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 H) (hc.intervalIntegrable H 1), hleft, hright]
  ring

/-- A small overlap cap forces a quantitatively small actual first moment. -/
theorem profileMean_abs_le_of_cap {h : ℝ → ℝ} {H : ℝ}
    (hh : Admissible h) (hcap : OverlapCap h H) (hH1 : H ≤ 1) :
    |profileMean (overlapProfile h)| ≤ 2*H-H^2 := by
  have hH0 : 0 ≤ H := hcap.nonneg hh
  have hnorm : |∫ t in (0 : ℝ)..1, overlapProfile h t| ≤
      ∫ t in (0 : ℝ)..1, min t H := by
    change ‖∫ t in (0 : ℝ)..1, overlapProfile h t‖ ≤
      ∫ t in (0 : ℝ)..1, min t H
    apply intervalIntegral.norm_integral_le_of_norm_le zero_le_one
      (Filter.Eventually.of_forall (fun t ht => ?_))
      ((continuous_id.min continuous_const).intervalIntegrable 0 1)
    change |overlapProfile h t| ≤ min t H
    exact overlapProfile_mem_kernelBox hh hcap le_rfl ⟨le_of_lt ht.1, ht.2⟩
  rw [integral_min_id_const hH0 hH1] at hnorm
  rw [profileMean, abs_mul]
  norm_num
  linarith

/-- Mean intervals strictly beyond the physical cap threshold are empty. -/
theorem not_overlapCap_of_profileMean_lower {h : ℝ → ℝ} {H l : ℝ}
    (hh : Admissible h) (hH1 : H ≤ 1) (hl : 2*H-H^2 < l)
    (hm : l ≤ profileMean (overlapProfile h)) : ¬ OverlapCap h H := by
  intro hcap
  have hb := profileMean_abs_le_of_cap hh hcap hH1
  exact (not_lt_of_ge ((le_abs_self _).trans hb)) (hl.trans_le hm)

/-- An impossible mean row is physically valid by the proved cap estimate.
There is no numerical kernel enclosure among the hypotheses. -/
theorem physicalMeanInequality_of_cap_threshold {r : Certificate.Row} {H : ℝ}
    (hH1 : H ≤ 1) (hlo : 2*H-H^2 < (r.lo : ℝ)) :
    PhysicalMeanInequality r H := by
  intro h hh hm _ hcap
  exact (not_overlapCap_of_profileMean_lower hh hH1 hlo hm hcap).elim

end
end ErdosOverlap
