/-
Copyright (c) 2026. Released under the BSD-3-Clause license.
-/
module

public import ErdosOverlap.KernelAssembly

/-! # Integrability and exact linearity of physical kernel expectations -/

namespace ErdosOverlap
open MeasureTheory Set
open scoped Interval
public section
noncomputable section

@[expose] def QuartetIntegrable (Q : ℝ → ℝ) : Prop :=
  ∀ ⦃h : ℝ → ℝ⦄, Admissible h → IntervalIntegrable (quartetIntegrand h Q) volume 0 1

theorem quartetIntegrand_add (h Q J : ℝ → ℝ) (t : ℝ) :
    quartetIntegrand h (fun x => Q x + J x) t =
      quartetIntegrand h Q t + quartetIntegrand h J t := by
  unfold quartetIntegrand
  ring

theorem quartetIntegrand_mul (h Q : ℝ → ℝ) (c t : ℝ) :
    quartetIntegrand h (fun x => c * Q x) t = c * quartetIntegrand h Q t := by
  unfold quartetIntegrand
  ring

theorem QuartetIntegrable.add {Q J : ℝ → ℝ}
    (hQ : QuartetIntegrable Q) (hJ : QuartetIntegrable J) :
    QuartetIntegrable (fun x => Q x + J x) := by
  intro h hh
  change IntervalIntegrable (fun t => quartetIntegrand h (fun x => Q x + J x) t) volume 0 1
  simpa only [quartetIntegrand_add] using (hQ hh).add (hJ hh)

theorem QuartetIntegrable.mul {Q : ℝ → ℝ}
    (hQ : QuartetIntegrable Q) (c : ℝ) : QuartetIntegrable (fun x => c * Q x) := by
  intro h hh
  change IntervalIntegrable (fun t => quartetIntegrand h (fun x => c * Q x) t) volume 0 1
  simpa only [quartetIntegrand_mul] using (hQ hh).const_mul c

theorem QuartetIntegrable.sub {Q J : ℝ → ℝ}
    (hQ : QuartetIntegrable Q) (hJ : QuartetIntegrable J) :
    QuartetIntegrable (fun x => Q x - J x) := by
  simpa only [neg_one_mul, sub_eq_add_neg] using hQ.add (hJ.mul (-1))

theorem quartetFunctional_add {h Q J : ℝ → ℝ} (hh : Admissible h)
    (hQ : QuartetIntegrable Q) (hJ : QuartetIntegrable J) :
    quartetFunctional h (fun x => Q x + J x) =
      quartetFunctional h Q + quartetFunctional h J := by
  simp only [quartetFunctional, quartetIntegrand_add]
  exact intervalIntegral.integral_add (hQ hh) (hJ hh)

theorem quartetFunctional_mul (h Q : ℝ → ℝ) (c : ℝ) :
    quartetFunctional h (fun x => c * Q x) = c * quartetFunctional h Q := by
  simp only [quartetFunctional, quartetIntegrand_mul, intervalIntegral.integral_const_mul]

theorem quartetFunctional_sub {h Q J : ℝ → ℝ} (hh : Admissible h)
    (hQ : QuartetIntegrable Q) (hJ : QuartetIntegrable J) :
    quartetFunctional h (fun x => Q x - J x) =
      quartetFunctional h Q - quartetFunctional h J := by
  have heq : (fun x => Q x - J x) = (fun x => Q x + (-1) * J x) := by funext x; ring
  rw [heq, quartetFunctional_add hh hQ (hJ.mul (-1)), quartetFunctional_mul]
  ring

theorem quartetIntegrable_of_bounded {Q : ℝ → ℝ} {C : ℝ}
    (hQ : Measurable Q) (hbound : ∀ t, |Q t| ≤ C) : QuartetIntegrable Q := by
  intro h hh
  have hp := positiveOverlap_weighted_intervalIntegrable hh hQ hbound
  have hn := negativeOverlap_weighted_intervalIntegrable hh
    (hQ.comp measurable_neg) (fun t => hbound (-t))
  simp only [Function.comp_apply, neg_neg] at hn
  let F := fun t => Q t * (positiveOverlap h t + negativeOverlap h t)
  have hF : IntervalIntegrable F volume 0 2 := by
    simpa only [F, mul_add] using hp.add hn
  have h01 : IntervalIntegrable F volume 0 1 := hF.mono_set (by
    simp only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1),
      uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)]
    intro t ht
    exact ⟨ht.1, by linarith [ht.2]⟩)
  have h12 : IntervalIntegrable F volume 1 2 := hF.mono_set (by
    simp only [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2),
      uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)]
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩)
  have hreflect : IntervalIntegrable (fun t => F (2 - t)) volume 0 1 := by
    convert h12.symm.comp_sub_left 2 using 1 <;> norm_num
  exact h01.add hreflect

theorem quartetIntegrable_of_boundedOn {Q : ℝ → ℝ} {C : ℝ}
    (hQ : Measurable Q) (hbound : ∀ t ∈ Icc (0 : ℝ) 2, |Q t| ≤ C) :
    QuartetIntegrable Q := by
  let J := (Icc (0 : ℝ) 2).indicator Q
  have hC : 0 ≤ C := (abs_nonneg (Q 0)).trans (hbound 0 (by norm_num))
  have hb : ∀ t, |J t| ≤ C := by
    intro t
    by_cases ht : t ∈ Icc (0 : ℝ) 2
    · simpa only [J, indicator_of_mem ht] using hbound t ht
    · simpa only [J, indicator_of_notMem ht, abs_zero] using hC
  have hJ := quartetIntegrable_of_bounded (hQ.indicator measurableSet_Icc) hb
  intro h hh
  apply (hJ hh).congr_uIoo
  intro t ht
  rw [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
  have ht' : t ∈ Icc (0 : ℝ) 2 := ⟨ht.1.le, by linarith [ht.2]⟩
  have hr : 2 - t ∈ Icc (0 : ℝ) 2 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  simp only [quartetIntegrand, indicator_of_mem ht', indicator_of_mem hr]

theorem quartetIntegrable_of_continuous {Q : ℝ → ℝ} (hQ : Continuous Q) :
    QuartetIntegrable Q := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 2)).exists_bound_of_continuousOn
    hQ.continuousOn
  exact quartetIntegrable_of_boundedOn hQ.measurable (by simpa only [Real.norm_eq_abs] using hC)

theorem periodicDilationKernel_quartetIntegrable (n k i : ℕ) :
    QuartetIntegrable (periodicDilationKernel n k i) :=
  quartetIntegrable_of_bounded
    (symmetrizeWeight_measurable (periodicDilationWeight_measurable n k i))
    (symmetrizeWeight_bound (periodicDilationWeight_bound n k i))

theorem phaseKernel_quartetIntegrable (n : ℕ) (gamma : Array ℚ) :
    QuartetIntegrable (phaseKernel n gamma) :=
  quartetIntegrable_of_continuous (phaseKernel_continuous n gamma)

end
end
end ErdosOverlap
