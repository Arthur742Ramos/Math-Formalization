/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.FrontierLeafCertificate
public import ErdosOverlap.FrontierNormalization
public import ErdosOverlap.ZeroWitness
public import ErdosOverlap.Constant

/-! Physical row realization from source-bound integral inequalities. -/

namespace ErdosOverlap.Frontier
open MeasureTheory FrontierWitnesses FrontierLeaves
public section

noncomputable def profileCertificate (r : Certificate.Row) (H D I : ℚ) (mode : Fin 20)
    (haux : FrontierLeaves.auxiliaryLevel ≤ H) (hcap : H ≤ FrontierLeaves.boxCap)
    (hH : 0 ≤ H) (hD : 0 < D)
    (hd : r.d = D) (ha : r.a = lowerAtZeroBound + I - modeIv mode)
    (hb : r.b = modeTau mode) (hc : r.c = FrontierData.meanCoefficientExact)
    (denominator : kernelDenominator kernel ≤ (D : ℝ))
    (integral : (I : ℝ) ≤ ∫ t in (0 : ℝ)..1, profileIntegrand mode t) :
    MeanKernelCertificate r (H : ℝ) where
  kernel := kernel
  witness := modeWitness mode
  auxiliaryLevel := (FrontierLeaves.auxiliaryLevel : ℝ)
  boxCap := (FrontierLeaves.boxCap : ℝ)
  tau := (modeTau mode : ℝ)
  lowerExpectation := lowerExpectation
  auxiliary_le_height := by exact_mod_cast haux
  height_le_boxCap := by exact_mod_cast hcap
  height_nonneg := by exact_mod_cast hH
  denominator_pos := by rw [hd]; exact_mod_cast hD
  denominator_upper := by rw [hd]; exact denominator
  witness_ac := modeWitness_absolutelyContinuous mode
  witness_end := modeWitness_one mode
  positive_integrable := positivePart_intervalIntegrable
  conjugate_integrable := profileIntegrand_integrable mode
  quartet_integrable := fun _ hh => kernel_quartetIntegrable hh
  cost_integrable := fun _ hh => cost_intervalIntegrable hh _
  expectation_bound := fun _ hh => lowerExpectation_le hh
  quantitative_return := by
    intro m _ _
    rw [ha, hb, hc]
    simp only [lowerExpectation, Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat]
    have hi := integral
    change _ ≤ ∫ t in (0 : ℝ)..1,
      kernelConjugate kernel (FrontierLeaves.auxiliaryLevel : ℝ)
        (FrontierLeaves.boxCap : ℝ) (modeTau mode : ℝ) (modeWitness mode) t at hi
    linarith [lowerAtZeroBound_le, modeWitness_integral_abs_le mode]

noncomputable def centralCertificate (r : Certificate.Row) (H D I : ℚ)
    (haux : FrontierLeaves.auxiliaryLevel ≤ H) (hcap : H ≤ FrontierLeaves.boxCap)
    (hH : 0 ≤ H) (hD : 0 < D)
    (hd : r.d = D) (ha : r.a = lowerAtZeroBound + I)
    (hb : r.b = 0) (hc : r.c = FrontierData.meanCoefficientExact)
    (denominator : kernelDenominator kernel ≤ (D : ℝ))
    (integral : (I : ℝ) ≤ ∫ t in (0 : ℝ)..1, centralIntegrand t) :
    MeanKernelCertificate r (H : ℝ) where
  kernel := kernel
  witness := fun _ => 0
  auxiliaryLevel := (FrontierLeaves.auxiliaryLevel : ℝ)
  boxCap := (FrontierLeaves.boxCap : ℝ)
  tau := 0
  lowerExpectation := lowerExpectation
  auxiliary_le_height := by exact_mod_cast haux
  height_le_boxCap := by exact_mod_cast hcap
  height_nonneg := by exact_mod_cast hH
  denominator_pos := by rw [hd]; exact_mod_cast hD
  denominator_upper := by rw [hd]; exact denominator
  witness_ac := zeroWitness_absolutelyContinuous
  witness_end := rfl
  positive_integrable := positivePart_intervalIntegrable
  conjugate_integrable := conjugate_intervalIntegrable zeroWitness_absolutelyContinuous _ _ _
  quartet_integrable := fun _ hh => kernel_quartetIntegrable hh
  cost_integrable := fun _ hh => cost_intervalIntegrable hh _
  expectation_bound := fun _ hh => lowerExpectation_le hh
  quantitative_return := by
    intro m _ _
    rw [ha, hb, hc, zeroWitness_abs_integral, integral_kernelConjugate_zero_witness]
    simp only [lowerExpectation, Rat.cast_add, Rat.cast_zero, zero_mul, add_zero, sub_zero]
    have hi := integral
    change _ ≤ ∫ t in (0 : ℝ)..1,
      max (kernel (2-t)) 0 * max (2*(FrontierLeaves.auxiliaryLevel : ℝ)-t) 0 at hi
    linarith [lowerAtZeroBound_le]

end
end ErdosOverlap.Frontier
