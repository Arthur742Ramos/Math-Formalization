/-
Copyright (c) 2026. Released under the BSD-3-Clause license.
-/
module

public import ErdosOverlap.KernelLinearity
public import ErdosOverlap.Native6Kernel

/-!
# Exact assembly of physical kernel expectation inequalities

The Fourier and periodic terms are discharged from admissibility here.
The general phase-list lemma accepts already proved individual physical
phase inequalities; the concrete native theorem supplies those proofs
from the exact PSD certificates.
-/

namespace ErdosOverlap
open MeasureTheory Set
open scoped Interval
public section
noncomputable section

theorem PeriodicCellRow.quartetIntegrable (n : ℕ) (row : PeriodicCellRow) :
    QuartetIntegrable (row.value n) := by
  have hr := periodicDilationKernel_quartetIntegrable n row.firstPosition row.cell
  have hk := periodicDilationKernel_quartetIntegrable n row.lastPosition row.cell
  have hd := periodicDilationKernel_quartetIntegrable n (row.lastPosition - row.firstPosition) row.cell
  change QuartetIntegrable (fun t => row.value n t)
  cases hp : row.perimeter
  · simpa only [PeriodicCellRow.value, hp, Bool.false_eq_true, ite_false] using
      ((hk.sub hr).sub hd).mul (row.weight : ℝ)
  · simpa only [PeriodicCellRow.value, hp, ite_true] using
      ((hr.add hd).add hk).mul (row.weight : ℝ)

theorem PeriodicCellRow.functional_lower_bound {h : ℝ → ℝ} (hh : Admissible h)
    {n : ℕ} (hn : 0 < n) (row : PeriodicCellRow) (hv : row.valid n = true) :
    (row.lowerValue : ℝ) ≤ quartetFunctional h (row.value n) := by
  have hhrow : 0 < row.firstPosition ∧ row.firstPosition < row.lastPosition ∧
      row.cell < n ∧ row.weight ≤ 0 := of_decide_eq_true hv
  have hz : (row.weight : ℝ) ≤ 0 := by exact_mod_cast hhrow.2.2.2
  have hr := periodicDilationKernel_quartetIntegrable n row.firstPosition row.cell
  have hk := periodicDilationKernel_quartetIntegrable n row.lastPosition row.cell
  have hd := periodicDilationKernel_quartetIntegrable n (row.lastPosition - row.firstPosition) row.cell
  change (row.lowerValue : ℝ) ≤ quartetFunctional h (fun t => row.value n t)
  cases hp : row.perimeter
  · simp only [PeriodicCellRow.value, PeriodicCellRow.lowerValue, hp, Bool.false_eq_true,
      ite_false, Rat.cast_zero]
    rw [quartetFunctional_mul, quartetFunctional_sub hh (hk.sub hr) hd,
      quartetFunctional_sub hh hk hr]
    exact periodic_grid_triangle_multiplier hh hn hhrow.1 hhrow.2.1 row.cell hz
  · simp only [PeriodicCellRow.value, PeriodicCellRow.lowerValue, hp,
      ite_true, Rat.cast_mul, Rat.cast_ofNat]
    rw [quartetFunctional_mul, quartetFunctional_add hh (hr.add hd) hk,
      quartetFunctional_add hh hr hd]
    exact periodic_grid_perimeter_multiplier hh hn hhrow.1 hhrow.2.1 row.cell hz

theorem periodicRowsKernel_quartetIntegrable (n : ℕ) (rows : List PeriodicCellRow) :
    QuartetIntegrable (periodicRowsKernel n rows) := by
  induction rows with
  | nil => exact quartetIntegrable_of_continuous continuous_const
  | cons row rows ih => exact (row.quartetIntegrable n).add ih

theorem periodicRowsKernel_lower_bound {h : ℝ → ℝ} (hh : Admissible h)
    {n : ℕ} (hn : 0 < n) (rows : List PeriodicCellRow)
    (hv : rows.all (PeriodicCellRow.valid n) = true) :
    (periodicRowsLower rows : ℝ) ≤ quartetFunctional h (periodicRowsKernel n rows) := by
  induction rows with
  | nil => simp [periodicRowsLower, periodicRowsKernel, quartetFunctional, quartetIntegrand]
  | cons row rows ih =>
    have hv' : row.valid n = true ∧ rows.all (PeriodicCellRow.valid n) = true := by
      simpa only [List.all_cons, Bool.and_eq_true] using hv
    change ((row.lowerValue + periodicRowsLower rows : ℚ) : ℝ) ≤
      quartetFunctional h (fun t => row.value n t + periodicRowsKernel n rows t)
    rw [Rat.cast_add, quartetFunctional_add hh (row.quartetIntegrable n)
      (periodicRowsKernel_quartetIntegrable n rows)]
    exact add_le_add (row.functional_lower_bound hh hn hv'.1) (ih hv'.2)

theorem PhaseFunctionalRow.quartetIntegrable (row : PhaseFunctionalRow) :
    QuartetIntegrable row.value :=
  (phaseKernel_quartetIntegrable row.cells row.gamma).mul (row.multiplier : ℝ)

theorem phaseRowsKernel_quartetIntegrable (rows : List PhaseFunctionalRow) :
    QuartetIntegrable (phaseRowsKernel rows) := by
  induction rows with
  | nil => exact quartetIntegrable_of_continuous continuous_const
  | cons row rows ih => exact row.quartetIntegrable.add ih

theorem phaseRowsKernel_lower_bound {h : ℝ → ℝ} (hh : Admissible h)
    (rows : List PhaseFunctionalRow) (hv : rows.all PhaseFunctionalRow.valid = true)
    (hphase : ∀ row ∈ rows,
      (row.lowerAtZero : ℝ) + (row.meanCoefficient : ℝ) * profileMean (overlapProfile h)^2 ≤
        quartetFunctional h (phaseKernel row.cells row.gamma)) :
    (phaseRowsLower rows : ℝ) + (phaseRowsMeanCoefficient rows : ℝ) *
        profileMean (overlapProfile h)^2 ≤ quartetFunctional h (phaseRowsKernel rows) := by
  induction rows with
  | nil => simp [phaseRowsLower, phaseRowsMeanCoefficient, phaseRowsKernel,
      quartetFunctional, quartetIntegrand]
  | cons row rows ih =>
    have hv' : row.valid = true ∧ rows.all PhaseFunctionalRow.valid = true := by
      simpa only [List.all_cons, Bool.and_eq_true] using hv
    have hrow : 0 < row.cells ∧ row.gamma.size = row.cells + 1 ∧ 0 ≤ row.multiplier :=
      of_decide_eq_true hv'.1
    have hmu : (0 : ℝ) ≤ (row.multiplier : ℝ) := by exact_mod_cast hrow.2.2
    have hrowbound := mul_le_mul_of_nonneg_left (hphase row List.mem_cons_self) hmu
    have hrest := ih hv'.2 (fun r hr => hphase r (List.mem_cons_of_mem row hr))
    have hadd := add_le_add hrowbound hrest
    change _ ≤ quartetFunctional h (fun t => row.value t + phaseRowsKernel rows t)
    rw [quartetFunctional_add hh row.quartetIntegrable (phaseRowsKernel_quartetIntegrable rows)]
    rw [show quartetFunctional h row.value = (row.multiplier : ℝ) *
      quartetFunctional h (phaseKernel row.cells row.gamma) from
      quartetFunctional_mul h (phaseKernel row.cells row.gamma) (row.multiplier : ℝ)]
    convert hadd using 1
    simp only [phaseRowsLower, phaseRowsMeanCoefficient, Rat.cast_add, Rat.cast_mul]
    ring

namespace Native6

theorem cosineLower_le_functional {h : ℝ → ℝ} (hh : Admissible h)
    (terms : List Numerics.CosineTerm) (hz : ∀ term ∈ terms, term.weight ≤ 0) :
    cosineLower terms ≤ quartetFunctional h (Numerics.cosineSum terms) := by
  induction terms with
  | nil => simp [cosineLower, Numerics.cosineSum, quartetFunctional, quartetIntegrand]
  | cons term terms ih =>
    have hr : QuartetIntegrable (fun t : ℝ => (term.weight : ℝ) *
        Real.cos ((term.frequency : ℝ) * t)) := quartetIntegrable_of_continuous
      (continuous_const.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id)))
    have hs := quartetIntegrable_of_continuous (Numerics.cosineSum_continuous terms)
    change (term.weight : ℝ) * Real.sinc (term.frequency : ℝ)^2 + cosineLower terms ≤
      quartetFunctional h (fun t => (term.weight : ℝ) * Real.cos ((term.frequency : ℝ) * t) +
        Numerics.cosineSum terms t)
    rw [quartetFunctional_add hh hr hs, quartetFunctional_mul]
    apply add_le_add
    · exact quartetFunctional_nonpositive_cosine_row hh (term.frequency : ℝ)
        (by exact_mod_cast hz term List.mem_cons_self)
    · exact ih (fun a ha => hz a (List.mem_cons_of_mem term ha))

theorem kernel_quartetIntegrable : QuartetIntegrable kernel :=
  ((((quartetIntegrable_of_continuous continuous_const).add
    (quartetIntegrable_of_continuous (continuous_const.mul (continuous_id.pow 2)))).add
    (quartetIntegrable_of_continuous (Numerics.cosineSum_continuous Native6Trig.terms))).add
    (periodicRowsKernel_quartetIntegrable Native6Data.cells Native6Data.periodicRows)).add
    (phaseRowsKernel_quartetIntegrable Native6Data.phaseRows)

theorem lowerExpectation_le_of_phase {h : ℝ → ℝ} (hh : Admissible h)
    (hphase : ∀ row ∈ Native6Data.phaseRows,
      (row.lowerAtZero : ℝ) + (row.meanCoefficient : ℝ) * profileMean (overlapProfile h)^2 ≤
        quartetFunctional h (phaseKernel row.cells row.gamma)) :
    lowerExpectation (profileMean (overlapProfile h)) ≤ quartetFunctional h kernel := by
  have h0 : QuartetIntegrable (fun _ : ℝ => (Native6Data.y0 : ℝ)) :=
    quartetIntegrable_of_continuous continuous_const
  have h2 : QuartetIntegrable (fun t : ℝ => (Native6Data.y2 : ℝ) * t^2) :=
    quartetIntegrable_of_continuous (continuous_const.mul (continuous_id.pow 2))
  have hcos := quartetIntegrable_of_continuous (Numerics.cosineSum_continuous Native6Trig.terms)
  have hperiodic := periodicRowsKernel_quartetIntegrable Native6Data.cells Native6Data.periodicRows
  have hphasei := phaseRowsKernel_quartetIntegrable Native6Data.phaseRows
  have hcosbound := cosineLower_le_functional hh Native6Trig.terms (by
    intro term ht
    have hchecked := (List.all_eq_true.mp Native6Trig.allNonpositive_checked) term ht
    exact (of_decide_eq_true hchecked).1)
  have hperiodicbound := periodicRowsKernel_lower_bound hh
    (by decide +kernel : 0 < Native6Data.cells) Native6Data.periodicRows Native6Data.periodicRows_valid
  have hphasebound := phaseRowsKernel_lower_bound hh Native6Data.phaseRows
    Native6Data.phaseRows_valid hphase
  have hconst : quartetFunctional h (fun _ : ℝ => (Native6Data.y0 : ℝ)) = (Native6Data.y0 : ℝ) := by
    have heq : (fun _ : ℝ => (Native6Data.y0 : ℝ)) = (fun _ : ℝ => (Native6Data.y0 : ℝ) * 1) := by
      funext t; ring
    rw [heq, quartetFunctional_mul, quartetFunctional_one hh, mul_one]
  have hsquare := quartetFunctional_sq hh
  unfold kernel
  rw [quartetFunctional_add hh (((h0.add h2).add hcos).add hperiodic) hphasei,
    quartetFunctional_add hh ((h0.add h2).add hcos) hperiodic,
    quartetFunctional_add hh (h0.add h2) hcos,
    quartetFunctional_add hh h0 h2,
    hconst, quartetFunctional_mul, hsquare]
  unfold lowerExpectation lowerAtZero algebraicLowerAtZero meanCoefficient
  push_cast
  linarith

end Native6
end
end
end ErdosOverlap
