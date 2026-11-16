/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.FrontierKernelData
public import ErdosOverlap.Certificate.FrontierTrigData
public import ErdosOverlap.KernelIntegrability
public import ErdosOverlap.Gram.Native6Phase

/-! # Physical expectation for the fully_joint32 kernel

Every coefficient below is the net coefficient of the physical kernel.
Signed corrections are used only for later function identities, never as
independent expectation inequalities. The existing phase matrices and their
proved physical meaning are unchanged; their nonnegative multipliers change.
-/

namespace ErdosOverlap.Frontier

open MeasureTheory
@[expose] public section
noncomputable section

def kernel (t : ℝ) : ℝ :=
  (FrontierData.y0 : ℝ) + (FrontierData.y2 : ℝ) * t ^ 2 +
    Numerics.cosineSum FrontierTrig.terms t +
    periodicRowsKernel Native6Data.cells FrontierData.periodicRows t +
    phaseRowsKernel FrontierData.phaseRows t

def lowerAtZero : ℝ :=
  (FrontierData.rationalPartExact : ℝ) + Native6.cosineLower FrontierTrig.terms

def lowerExpectation (m : ℝ) : ℝ :=
  lowerAtZero + (FrontierData.meanCoefficientExact : ℝ) * m ^ 2

theorem phase_functional {h : ℝ → ℝ} (hh : Admissible h)
    (row : PhaseFunctionalRow) (hr : row ∈ FrontierData.phaseRows) :
    (row.lowerAtZero : ℝ) + (row.meanCoefficient : ℝ) *
        profileMean (overlapProfile h)^2 ≤
      quartetFunctional h (phaseKernel row.cells row.gamma) := by
  simp only [FrontierData.phaseRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Gram.Native6Phase00.functional_lower_bound hh
  · exact Gram.Native6Phase01.functional_lower_bound hh
  · exact Gram.Native6Phase02.functional_lower_bound hh
  · exact Gram.Native6Phase03.functional_lower_bound hh
  · exact Gram.Native6Phase04.functional_lower_bound hh
  · exact Gram.Native6Phase05.functional_lower_bound hh
  · exact Gram.Native6Phase06.functional_lower_bound hh
  · exact Gram.Native6Phase07.functional_lower_bound hh
  · exact Gram.Native6Phase08.functional_lower_bound hh
  · exact Gram.Native6Phase09.functional_lower_bound hh
  · exact Gram.Native6Phase10.functional_lower_bound hh
  · exact Gram.Native6Phase11.functional_lower_bound hh
  · exact Gram.Native6Phase12.functional_lower_bound hh
  · exact Gram.Native6Phase13.functional_lower_bound hh
  · exact Gram.Native6Phase14.functional_lower_bound hh
  · exact Gram.Native6Phase15.functional_lower_bound hh
  · exact Gram.Native6Phase16.functional_lower_bound hh
  · exact Gram.Native6Phase17.functional_lower_bound hh
  · exact Gram.Native6Phase18.functional_lower_bound hh
  · exact Gram.Native6Phase19.functional_lower_bound hh
  · exact Gram.Native6Phase20.functional_lower_bound hh
  · exact Gram.Native6Phase21.functional_lower_bound hh
  · exact Gram.Native6Phase22.functional_lower_bound hh

theorem kernel_quartetIntegrable : QuartetIntegrable kernel :=
  ((((quartetIntegrable_of_continuous continuous_const).add
    (quartetIntegrable_of_continuous (continuous_const.mul (continuous_id.pow 2)))).add
    (quartetIntegrable_of_continuous (Numerics.cosineSum_continuous FrontierTrig.terms))).add
    (periodicRowsKernel_quartetIntegrable Native6Data.cells FrontierData.periodicRows)).add
    (phaseRowsKernel_quartetIntegrable FrontierData.phaseRows)

theorem lowerExpectation_le {h : ℝ → ℝ} (hh : Admissible h) :
    lowerExpectation (profileMean (overlapProfile h)) ≤ quartetFunctional h kernel := by
  have h0 : QuartetIntegrable (fun _ : ℝ => (FrontierData.y0 : ℝ)) :=
    quartetIntegrable_of_continuous continuous_const
  have h2 : QuartetIntegrable (fun t : ℝ => (FrontierData.y2 : ℝ) * t ^ 2) :=
    quartetIntegrable_of_continuous (continuous_const.mul (continuous_id.pow 2))
  have hcos := quartetIntegrable_of_continuous (Numerics.cosineSum_continuous FrontierTrig.terms)
  have hp := periodicRowsKernel_quartetIntegrable Native6Data.cells FrontierData.periodicRows
  have hg := phaseRowsKernel_quartetIntegrable FrontierData.phaseRows
  have hcosbound := Native6.cosineLower_le_functional hh FrontierTrig.terms (by
    intro term ht
    have hc := (List.all_eq_true.mp FrontierTrig.allNonpositive_checked) term ht
    exact (of_decide_eq_true hc).1)
  have hpbound := periodicRowsKernel_lower_bound hh
    (by decide +kernel : 0 < Native6Data.cells)
    FrontierData.periodicRows FrontierData.periodicRows_valid
  have hgbound := phaseRowsKernel_lower_bound hh FrontierData.phaseRows
    FrontierData.phaseRows_valid (fun row hr => phase_functional hh row hr)
  have hconst : quartetFunctional h (fun _ : ℝ => (FrontierData.y0 : ℝ)) =
      (FrontierData.y0 : ℝ) := by
    have heq : (fun _ : ℝ => (FrontierData.y0 : ℝ)) =
        (fun _ : ℝ => (FrontierData.y0 : ℝ) * 1) := by
      funext t
      ring
    rw [heq, quartetFunctional_mul, quartetFunctional_one hh, mul_one]
  unfold kernel
  rw [quartetFunctional_add hh (((h0.add h2).add hcos).add hp) hg,
    quartetFunctional_add hh ((h0.add h2).add hcos) hp,
    quartetFunctional_add hh (h0.add h2) hcos,
    quartetFunctional_add hh h0 h2, hconst, quartetFunctional_mul,
    quartetFunctional_sq hh]
  unfold lowerExpectation lowerAtZero
  rw [← FrontierData.algebraic_part_checked, ← FrontierData.mean_coefficient_checked]
  push_cast
  linarith

theorem kernel_intervalIntegrable (a b : ℝ) : IntervalIntegrable kernel volume a b := by
  have h0 : IntervalIntegrable (fun _ : ℝ => (FrontierData.y0 : ℝ)) volume a b :=
    intervalIntegrable_const
  have h2 : IntervalIntegrable (fun t : ℝ => (FrontierData.y2 : ℝ) * t ^ 2) volume a b :=
    (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable a b
  have hc := (Numerics.cosineSum_continuous FrontierTrig.terms).intervalIntegrable (μ := volume) a b
  have hp := periodicRowsKernel_intervalIntegrable Native6Data.cells FrontierData.periodicRows a b
  have hg := (phaseRowsKernel_continuous FrontierData.phaseRows).intervalIntegrable (μ := volume) a b
  exact (((h0.add h2).add hc).add hp).add hg

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

end
end
end ErdosOverlap.Frontier
