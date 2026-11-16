/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.FourierKernel

/-!
# Exact color-complement symmetry

Swapping the two colors reverses the physical signed mean, preserves every
common overlap cap, and leaves every even quartet functional unchanged.
-/

namespace ErdosOverlap

open MeasureTheory Set

public section
noncomputable section

theorem positiveOverlap_complement (h : ℝ → ℝ) (t : ℝ) :
    positiveOverlap (fun x => 1 - h x) t = negativeOverlap h t := by
  unfold positiveOverlap negativeOverlap
  apply intervalIntegral.integral_congr
  intro x _
  ring

theorem negativeOverlap_complement (h : ℝ → ℝ) (t : ℝ) :
    negativeOverlap (fun x => 1 - h x) t = positiveOverlap h t := by
  unfold positiveOverlap negativeOverlap
  apply intervalIntegral.integral_congr
  intro x _
  ring

theorem profileSlope_complement (h : ℝ → ℝ) (t : ℝ) :
    profileSlope (fun x => 1 - h x) t = -profileSlope h t := by
  unfold profileSlope
  ring

theorem overlapProfile_complement (h : ℝ → ℝ) (t : ℝ) :
    overlapProfile (fun x => 1 - h x) t = -overlapProfile h t := by
  unfold overlapProfile
  simp_rw [profileSlope_complement, intervalIntegral.integral_neg]

theorem profileMean_complement (h : ℝ → ℝ) :
    profileMean (overlapProfile (fun x => 1 - h x)) = -profileMean (overlapProfile h) := by
  unfold profileMean
  simp_rw [overlapProfile_complement, intervalIntegral.integral_neg]
  ring

theorem OverlapCap.complement {h : ℝ → ℝ} {M : ℝ} (hcap : OverlapCap h M) :
    OverlapCap (fun x => 1 - h x) M := by
  intro t ht
  rw [positiveOverlap_complement, negativeOverlap_complement]
  exact ⟨(hcap t ht).2, (hcap t ht).1⟩

theorem quartetFunctional_complement (h Q : ℝ → ℝ) :
    quartetFunctional (fun x => 1 - h x) Q = quartetFunctional h Q := by
  unfold quartetFunctional
  apply intervalIntegral.integral_congr
  intro t _
  simp only [quartetIntegrand, positiveOverlap_complement, negativeOverlap_complement]
  ring

/-- Every physical configuration has a color labeling with nonnegative mean
and the identical cap and even-kernel expectations. -/
theorem exists_nonnegative_mean_same_cap {h : ℝ → ℝ} {M : ℝ}
    (hh : Admissible h) (hcap : OverlapCap h M) :
    ∃ g : ℝ → ℝ, Admissible g ∧ OverlapCap g M ∧
      profileMean (overlapProfile g) = |profileMean (overlapProfile h)| ∧
      ∀ Q : ℝ → ℝ, quartetFunctional g Q = quartetFunctional h Q := by
  by_cases hm : 0 ≤ profileMean (overlapProfile h)
  · refine ⟨h, hh, hcap, ?_, fun _ => rfl⟩
    rw [abs_of_nonneg hm]
  · refine ⟨fun x => 1 - h x, hh.complement, hcap.complement, ?_, ?_⟩
    · rw [profileMean_complement, abs_of_nonpos (le_of_not_ge hm)]
    · exact quartetFunctional_complement h

end
end
end ErdosOverlap
