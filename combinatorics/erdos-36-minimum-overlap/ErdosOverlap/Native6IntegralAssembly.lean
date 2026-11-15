/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.NativeLeafCertificate
public import ErdosOverlap.Certificate.CoarseNative6Integrals
public import ErdosOverlap.Certificate.CoarseNative6Reflection
public import ErdosOverlap.Certificate.Native6Grid.SincChecks
public import ErdosOverlap.Native6Expectation

/-!
# Actual native physical rows from explicit integral enclosures

All physical expectation, witness, normalization and integrability facts are
discharged here. The remaining input consists solely of the stated numerical
integral inequalities for the actual native kernel and the actual witnesses.
The leaf certificate replay must construct this input before the numerical
constant theorem is unconditional.
-/

@[expose] public section

namespace ErdosOverlap.Certificate.CoarseNative6

open MeasureTheory Native6Witnesses Native6Leaves

structure NativeIntegralBounds : Prop where
  denominator : kernelDenominator Native6.kernel ≤ (nativeDenominatorBound : ℝ)
  central : (centralIntegralLower : ℝ) ≤ ∫ t in (0 : ℝ)..1, centralIntegrand t
  profiles : ∀ mode : Fin 10, (profileIntegralLower mode : ℝ) ≤
    ∫ t in (0 : ℝ)..1, profileIntegrand mode t

theorem lowerAtZeroBound_le : (lowerAtZeroBound : ℝ) ≤ Native6.lowerAtZero := by
  simpa only [lowerAtZeroBound, Native6Grid.checkedLowerAtZero] using
    Native6Grid.lowerAtZero_checked

noncomputable def profileCertificate (bounds : NativeIntegralBounds) (mode : Fin 10) :
    MeanKernelCertificate (profileRow mode) (auxiliaryHeight : ℝ) where
  kernel := Native6.kernel
  witness := modeWitness mode
  auxiliaryLevel := (Native6Leaves.auxiliaryLevel : ℝ)
  boxCap := (Native6Leaves.boxCap : ℝ)
  tau := (modeTau mode : ℝ)
  lowerExpectation := Native6.lowerExpectation
  auxiliary_le_height := by norm_num [Native6Leaves.auxiliaryLevel, auxiliaryHeight]
  height_le_boxCap := by norm_num [Native6Leaves.boxCap, auxiliaryHeight]
  height_nonneg := by norm_num [auxiliaryHeight]
  denominator_pos := by
    rw [(profile_parameters mode).2.2.2]
    norm_num [nativeDenominatorBound]
  denominator_upper := by
    rw [(profile_parameters mode).2.2.2]
    exact bounds.denominator
  witness_ac := modeWitness_absolutelyContinuous mode
  witness_end := modeWitness_one mode
  positive_integrable := Native6.positivePart_intervalIntegrable
  conjugate_integrable := profileIntegrand_integrable mode
  quartet_integrable := fun _ hh => Native6.kernel_quartetIntegrable hh
  cost_integrable := fun _ hh => Native6.cost_intervalIntegrable hh _
  expectation_bound := fun _ hh => Native6.lowerExpectation_le hh
  quantitative_return := by
    intro m _ _
    rcases profile_parameters mode with ⟨ha,hb,hc,_⟩
    rw [ha,hb,hc,modeWitness_integral_abs]
    simp only [Native6.lowerExpectation, Native6.meanCoefficient_exact,
      Rat.cast_add, Rat.cast_sub]
    have hi := bounds.profiles mode
    change _ ≤ ∫ t in (0 : ℝ)..1,
      kernelConjugate Native6.kernel (Native6Leaves.auxiliaryLevel : ℝ)
        (Native6Leaves.boxCap : ℝ) (modeTau mode : ℝ) (modeWitness mode) t at hi
    linarith [lowerAtZeroBound_le]

noncomputable def centralCertificate (bounds : NativeIntegralBounds) :
    MeanKernelCertificate nativeCentral (auxiliaryHeight : ℝ) where
  kernel := Native6.kernel
  witness := fun _ => 0
  auxiliaryLevel := (Native6Leaves.auxiliaryLevel : ℝ)
  boxCap := (Native6Leaves.boxCap : ℝ)
  tau := 0
  lowerExpectation := Native6.lowerExpectation
  auxiliary_le_height := by norm_num [Native6Leaves.auxiliaryLevel, auxiliaryHeight]
  height_le_boxCap := by norm_num [Native6Leaves.boxCap, auxiliaryHeight]
  height_nonneg := by norm_num [auxiliaryHeight]
  denominator_pos := by rw [central_parameters.2.2.2]; norm_num [nativeDenominatorBound]
  denominator_upper := by rw [central_parameters.2.2.2]; exact bounds.denominator
  witness_ac := zeroWitness_absolutelyContinuous
  witness_end := rfl
  positive_integrable := Native6.positivePart_intervalIntegrable
  conjugate_integrable := Native6.conjugate_intervalIntegrable zeroWitness_absolutelyContinuous _ _ _
  quartet_integrable := fun _ hh => Native6.kernel_quartetIntegrable hh
  cost_integrable := fun _ hh => Native6.cost_intervalIntegrable hh _
  expectation_bound := fun _ hh => Native6.lowerExpectation_le hh
  quantitative_return := by
    intro m _ _
    rcases central_parameters with ⟨ha,hb,hc,_⟩
    rw [ha,hb,hc,zeroWitness_abs_integral,integral_kernelConjugate_zero_witness]
    simp only [Native6.lowerExpectation, Native6.meanCoefficient_exact,
      Rat.cast_add, Rat.cast_zero, zero_mul, add_zero, sub_zero]
    have hi := bounds.central
    change _ ≤ ∫ t in (0 : ℝ)..1,
      max (Native6.kernel (2-t)) 0*max (2*(Native6Leaves.auxiliaryLevel : ℝ)-t) 0 at hi
    linarith [lowerAtZeroBound_le]

theorem nativeRows_physical (bounds : NativeIntegralBounds) :
    PhysicalMeanInequalities nativeRows auxiliaryHeight := by
  intro r hr
  simp only [nativeRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (centralCertificate bounds).physicalMeanInequality
  · exact (profileCertificate bounds ⟨0,by decide⟩).physicalMeanInequality
  · exact (profileCertificate bounds ⟨1,by decide⟩).physicalMeanInequality
  · exact (profileCertificate bounds ⟨2,by decide⟩).physicalMeanInequality
  · exact (profileCertificate bounds ⟨3,by decide⟩).physicalMeanInequality
  · exact (profileCertificate bounds ⟨4,by decide⟩).physicalMeanInequality
  · exact (profileCertificate bounds ⟨5,by decide⟩).physicalMeanInequality
  · exact (profileCertificate bounds ⟨6,by decide⟩).physicalMeanInequality
  · exact (profileCertificate bounds ⟨7,by decide⟩).physicalMeanInequality
  · exact (profileCertificate bounds ⟨8,by decide⟩).physicalMeanInequality
  · exact (profileCertificate bounds ⟨9,by decide⟩).physicalMeanInequality

theorem headline_lt_of_native_integrals_and_outer
    (bounds : NativeIntegralBounds)
    (outer : PhysicalMeanInequalities outerRows auxiliaryHeight) :
    (headlineTarget : ℝ) < erdosOverlapConstant := by
  apply headline_lt_erdosConstant_of_positive
  intro r hr
  rcases List.mem_append.mp hr with hn | ho
  · exact nativeRows_physical bounds r hn
  · exact outer r ho

end ErdosOverlap.Certificate.CoarseNative6
