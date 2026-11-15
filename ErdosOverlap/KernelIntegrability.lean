/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.KernelExpectation
public import ErdosOverlap.PiecewiseLinear
public import Mathlib.Topology.Order.Lattice

/-!
# Integrability of the actual native dual expressions

An integrable kernel on `[0,2]` suffices for all positive-part and profile
cost expressions. The conjugate also needs only an absolutely continuous
witness: its derivative is integrable, and the remaining capacity factors
are continuous on the compact integration interval. No unproved numerical
bound on the derivative is required.
-/

@[expose] public section

namespace ErdosOverlap

open MeasureTheory Set

theorem intervalIntegrable_positivePart {f : ℝ → ℝ} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun t => max (f t) 0) volume a b := by
  have hi := (hf.add hf.abs).div_const (2 : ℝ)
  have heq : (fun t => max (f t) 0) = (fun t => (f t + |f t|)/2) := by
    funext t
    by_cases ht : 0 ≤ f t
    · rw [max_eq_left ht, abs_of_nonneg ht]
      ring
    · rw [max_eq_right (le_of_not_ge ht), abs_of_nonpos (le_of_not_ge ht)]
      ring
  rw [heq]
  exact hi

theorem kernel_halves_intervalIntegrable {Q : ℝ → ℝ}
    (hQ : IntervalIntegrable Q volume 0 2) :
    IntervalIntegrable Q volume 0 1 ∧
      IntervalIntegrable (fun t => Q (2-t)) volume 0 1 := by
  have h01 : IntervalIntegrable Q volume 0 1 := hQ.mono_set (by
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1),
      uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)]
    intro t ht
    exact ⟨ht.1, by linarith [ht.2]⟩)
  have h12 : IntervalIntegrable Q volume 1 2 := hQ.mono_set (by
    rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2),
      uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)]
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩)
  refine ⟨h01, ?_⟩
  convert h12.symm.comp_sub_left 2 using 1 <;> norm_num

theorem kernel_positivePart_intervalIntegrable {Q : ℝ → ℝ}
    (hQ : IntervalIntegrable Q volume 0 2) :
    IntervalIntegrable
      (fun t => max (Q t) 0 + max (Q (2-t)) 0) volume 0 1 := by
  obtain ⟨hA, hB⟩ := kernel_halves_intervalIntegrable hQ
  exact (intervalIntegrable_positivePart hA).add (intervalIntegrable_positivePart hB)

theorem kernelCost_intervalIntegrable {h Q : ℝ → ℝ}
    (hh : Admissible h) (hQ : IntervalIntegrable Q volume 0 2) (a : ℝ) :
    IntervalIntegrable (kernelCost h Q a) volume 0 1 := by
  obtain ⟨hA, hB⟩ := kernel_halves_intervalIntegrable hQ
  have hd : ContinuousOn (fun t => |overlapProfile h t|) (uIcc (0 : ℝ) 1) :=
    (overlapProfile_lipschitz hh).continuousOn.abs
  have hL : ContinuousOn (fun t : ℝ => max (2*a-t) 0) (uIcc (0 : ℝ) 1) :=
    ((continuous_const.sub continuous_id).max continuous_const).continuousOn
  have hfirst := (hA.abs.add hB.abs).mul_continuousOn hd
  have hsecond : IntervalIntegrable
      (fun t => max (Q (2-t)) 0 * max (max (2*a-t) 0 - |overlapProfile h t|) 0)
      volume 0 1 := (intervalIntegrable_positivePart hB).mul_continuousOn
    ((hL.sub hd).sup continuousOn_const)
  exact hfirst.add hsecond

theorem kernelConjugate_intervalIntegrable {Q v : ℝ → ℝ}
    (hQ : IntervalIntegrable Q volume 0 2)
    (hv : AbsolutelyContinuousOnInterval v 0 1) (a H tau : ℝ) :
    IntervalIntegrable (kernelConjugate Q a H tau v) volume 0 1 := by
  obtain ⟨hA, hB⟩ := kernel_halves_intervalIntegrable hQ
  have hlam : IntervalIntegrable (dualSlope tau v) volume 0 1 :=
    intervalIntegrable_const.add hv.intervalIntegrable_deriv
  have hc := hA.abs.add hB.abs
  have hb := intervalIntegrable_positivePart hB
  have hhinge₁ := intervalIntegrable_positivePart ((hlam.abs.sub hc).add hb)
  have hhinge₂ := intervalIntegrable_positivePart (hlam.abs.sub hc)
  have hL : ContinuousOn (fun t : ℝ => max (2*a-t) 0) (uIcc (0 : ℝ) 1) :=
    ((continuous_const.sub continuous_id).max continuous_const).continuousOn
  have hU : ContinuousOn (fun t : ℝ => min t H) (uIcc (0 : ℝ) 1) :=
    (continuous_id.min continuous_const).continuousOn
  have hK := hU.inf hL
  have hV := hU.sub hK
  exact ((hb.mul_continuousOn hL).sub (hhinge₁.continuousOn_mul hK)).sub
    (hhinge₂.continuousOn_mul hV)

theorem intervalIntegrable_of_global_abs_bound {f : ℝ → ℝ} {C : ℝ}
    (hf : Measurable f) (hbound : ∀ t, |f t| ≤ C) (a b : ℝ) :
    IntervalIntegrable f volume a b := by
  have hC : 0 ≤ C := (abs_nonneg (f 0)).trans (hbound 0)
  rcases le_total a b with hab | hba
  · exact intervalIntegrable_of_abs_le hf hab hC (fun t _ => hbound t)
  · exact (intervalIntegrable_of_abs_le hf hba hC (fun t _ => hbound t)).symm

theorem periodicDilationKernel_intervalIntegrable (n k i : ℕ) (a b : ℝ) :
    IntervalIntegrable (periodicDilationKernel n k i) volume a b :=
  intervalIntegrable_of_global_abs_bound
    (symmetrizeWeight_measurable (periodicDilationWeight_measurable n k i))
    (symmetrizeWeight_bound (periodicDilationWeight_bound n k i)) a b

theorem PeriodicCellRow.intervalIntegrable (n : ℕ) (row : PeriodicCellRow) (a b : ℝ) :
    IntervalIntegrable (row.value n) volume a b := by
  have hfirst := periodicDilationKernel_intervalIntegrable n row.firstPosition row.cell a b
  have hlast := periodicDilationKernel_intervalIntegrable n row.lastPosition row.cell a b
  have hdiff := periodicDilationKernel_intervalIntegrable n
    (row.lastPosition-row.firstPosition) row.cell a b
  unfold PeriodicCellRow.value
  split_ifs
  · exact ((hfirst.add hdiff).add hlast).const_mul (row.weight : ℝ)
  · exact ((hlast.sub hfirst).sub hdiff).const_mul (row.weight : ℝ)

theorem periodicRowsKernel_intervalIntegrable (n : ℕ) (rows : List PeriodicCellRow)
    (a b : ℝ) : IntervalIntegrable (periodicRowsKernel n rows) volume a b := by
  induction rows with
  | nil => exact intervalIntegrable_const
  | cons row rest ih => exact (row.intervalIntegrable n a b).add ih

theorem phaseRowsKernel_continuous (rows : List PhaseFunctionalRow) :
    Continuous (phaseRowsKernel rows) := by
  induction rows with
  | nil => exact continuous_const
  | cons row rest ih =>
    exact (continuous_const.mul (phaseKernel_continuous row.cells row.gamma)).add ih

namespace Native6

theorem kernel_intervalIntegrable (a b : ℝ) : IntervalIntegrable kernel volume a b := by
  have h0 : IntervalIntegrable (fun _ : ℝ => (Native6Data.y0 : ℝ)) volume a b :=
    intervalIntegrable_const
  have h2 : IntervalIntegrable (fun t : ℝ => (Native6Data.y2 : ℝ)*t^2) volume a b :=
    (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable a b
  have hcos := (Numerics.cosineSum_continuous Native6Trig.terms).intervalIntegrable (μ := volume) a b
  have hperiod := periodicRowsKernel_intervalIntegrable Native6Data.cells Native6Data.periodicRows a b
  have hphase := (phaseRowsKernel_continuous Native6Data.phaseRows).intervalIntegrable (μ := volume) a b
  exact (((h0.add h2).add hcos).add hperiod).add hphase

theorem positivePart_intervalIntegrable : IntervalIntegrable
    (fun t => max (kernel t) 0 + max (kernel (2-t)) 0) volume 0 1 :=
  kernel_positivePart_intervalIntegrable (kernel_intervalIntegrable 0 2)

theorem cost_intervalIntegrable {h : ℝ → ℝ} (hh : Admissible h) (a : ℝ) :
    IntervalIntegrable (kernelCost h kernel a) volume 0 1 :=
  kernelCost_intervalIntegrable hh (kernel_intervalIntegrable 0 2) a

theorem conjugate_intervalIntegrable {v : ℝ → ℝ}
    (hv : AbsolutelyContinuousOnInterval v 0 1) (a H tau : ℝ) :
    IntervalIntegrable (kernelConjugate kernel a H tau v) volume 0 1 :=
  kernelConjugate_intervalIntegrable (kernel_intervalIntegrable 0 2) hv a H tau

theorem pl_conjugate_intervalIntegrable (n den : ℕ) (nodes : List PLNode) (a H tau : ℝ) :
    IntervalIntegrable (kernelConjugate kernel a H tau (plWitness n den nodes)) volume 0 1 :=
  conjugate_intervalIntegrable (plWitness_absolutelyContinuous n den nodes) a H tau

end Native6
end ErdosOverlap
