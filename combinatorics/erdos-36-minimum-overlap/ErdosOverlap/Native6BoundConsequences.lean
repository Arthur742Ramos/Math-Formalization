/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Native6IntegralAssembly
public import ErdosOverlap.Certificate.CoarseNative6OuterReduction

/-!
# Full auxiliary-height consequences of the native certificate interface

These assembly lemmas retain the actual native-integral and outer-row proof
inputs. They expose the stronger non-strict auxiliary-height lower bound for
both continuous infima, as well as a strict bound for every individual peak.
The original discrete partition problem is addressed separately by its cell
embedding; no equality of continuous and discrete constants is assumed here.
-/

@[expose] public section

namespace ErdosOverlap.Certificate.CoarseNative6

theorem allRows_physical_of_native_integrals_and_needed
    (bounds : NativeIntegralBounds)
    (outer : PhysicalMeanInequalities outerRowsNeedingIntegrals auxiliaryHeight) :
    PhysicalMeanInequalities allRows auxiliaryHeight := by
  apply allRows_physical_of_positive
  intro r hr
  rcases List.mem_append.mp hr with hn | ho
  · exact nativeRows_physical bounds r hn
  · exact outerRows_physical_of_needed outer r ho

theorem peak_gt_auxiliaryHeight_of_native_integrals_and_needed
    (bounds : NativeIntegralBounds)
    (outer : PhysicalMeanInequalities outerRowsNeedingIntegrals auxiliaryHeight)
    {h : ℝ → ℝ} (hh : Admissible h) :
    (auxiliaryHeight : ℝ) < overlapPeak h :=
  overlapPeak_gt_of_physicalMeanCover allRows_chain allRows_valid
    (allRows_physical_of_native_integrals_and_needed bounds outer) hh

theorem auxiliaryHeight_le_relaxedConstant_of_native_integrals_and_needed
    (bounds : NativeIntegralBounds)
    (outer : PhysicalMeanInequalities outerRowsNeedingIntegrals auxiliaryHeight) :
    (auxiliaryHeight : ℝ) ≤ relaxedOverlapConstant :=
  le_relaxedConstant_of_physicalMeanCover allRows_chain allRows_valid
    (allRows_physical_of_native_integrals_and_needed bounds outer)

theorem auxiliaryHeight_le_erdosConstant_of_native_integrals_and_needed
    (bounds : NativeIntegralBounds)
    (outer : PhysicalMeanInequalities outerRowsNeedingIntegrals auxiliaryHeight) :
    (auxiliaryHeight : ℝ) ≤ erdosOverlapConstant :=
  (auxiliaryHeight_le_relaxedConstant_of_native_integrals_and_needed bounds outer).trans
    relaxedOverlapConstant_le_erdosOverlapConstant

theorem headline_lt_relaxedConstant_of_native_integrals_and_needed
    (bounds : NativeIntegralBounds)
    (outer : PhysicalMeanInequalities outerRowsNeedingIntegrals auxiliaryHeight) :
    (headlineTarget : ℝ) < relaxedOverlapConstant :=
  ((Rat.cast_lt (K := ℝ)).2 height_order.2.2.1).trans_le
    (auxiliaryHeight_le_relaxedConstant_of_native_integrals_and_needed bounds outer)

end ErdosOverlap.Certificate.CoarseNative6
