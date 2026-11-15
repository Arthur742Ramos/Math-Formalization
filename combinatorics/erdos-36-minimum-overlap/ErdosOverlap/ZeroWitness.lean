/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.KernelDual

/-!
# The boundary correction as a zero profile witness

At zero witness and zero mean multiplier, the exact conjugate is simply
the positive reflected kernel times the positive boundary slack. This
identity lets the central numerical row use the same full kernel mass and
the same physical dual theorem as the nonzero profile rows.
-/

@[expose] public section

namespace ErdosOverlap

open MeasureTheory

theorem zeroWitness_absolutelyContinuous :
    AbsolutelyContinuousOnInterval (fun _ : ℝ => (0 : ℝ)) 0 1 :=
  (LipschitzWith.const (0 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval

theorem zeroWitness_abs_integral :
    (∫ _t in (0 : ℝ)..1, |(0 : ℝ)|) = 0 := by simp

theorem kernelConjugate_zero_witness (Q : ℝ → ℝ) (a H t : ℝ) :
    kernelConjugate Q a H 0 (fun _ => 0) t =
      max (Q (2-t)) 0 * max (2*a-t) 0 := by
  have hb : max (Q (2-t)) 0 ≤ |Q (2-t)| :=
    max_le (le_abs_self _) (abs_nonneg _)
  have hfirst : -(|Q t| + |Q (2-t)|) + max (Q (2-t)) 0 ≤ 0 := by
    linarith [abs_nonneg (Q t)]
  have hsecond : -(|Q t| + |Q (2-t)|) ≤ 0 := by
    linarith [abs_nonneg (Q t), abs_nonneg (Q (2-t))]
  simp only [kernelConjugate, dualSlope, deriv_const, mul_zero, add_zero,
    profileConjugate, abs_zero, zero_sub, max_eq_right hfirst,
    max_eq_right hsecond, sub_zero]

theorem integral_kernelConjugate_zero_witness (Q : ℝ → ℝ) (a H : ℝ) :
    (∫ t in (0 : ℝ)..1, kernelConjugate Q a H 0 (fun _ => 0) t) =
      ∫ t in (0 : ℝ)..1, max (Q (2-t)) 0 * max (2*a-t) 0 := by
  simp_rw [kernelConjugate_zero_witness]

theorem kernelConjugate_zero_witness_intervalIntegrable
    (Q : ℝ → ℝ) (a H : ℝ)
    (hi : IntervalIntegrable
      (fun t => max (Q (2-t)) 0 * max (2*a-t) 0) volume 0 1) :
    IntervalIntegrable (kernelConjugate Q a H 0 (fun _ => 0)) volume 0 1 := by
  have heq : kernelConjugate Q a H 0 (fun _ => 0) =
      (fun t => max (Q (2-t)) 0 * max (2*a-t) 0) := by
    funext t
    exact kernelConjugate_zero_witness Q a H t
  rw [heq]
  exact hi

end ErdosOverlap
