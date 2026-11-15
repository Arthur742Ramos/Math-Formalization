/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Gram.Native6Phase00
public import ErdosOverlap.Gram.Native6Phase01
public import ErdosOverlap.Gram.Native6Phase02
public import ErdosOverlap.Gram.Native6Phase03
public import ErdosOverlap.Gram.Native6Phase04
public import ErdosOverlap.Gram.Native6Phase05
public import ErdosOverlap.Gram.Native6Phase06
public import ErdosOverlap.Gram.Native6Phase07
public import ErdosOverlap.Gram.Native6Phase08
public import ErdosOverlap.Gram.Native6Phase09
public import ErdosOverlap.Gram.Native6Phase10
public import ErdosOverlap.Gram.Native6Phase11
public import ErdosOverlap.Gram.Native6Phase12
public import ErdosOverlap.Gram.Native6Phase13
public import ErdosOverlap.Gram.Native6Phase14
public import ErdosOverlap.Gram.Native6Phase15
public import ErdosOverlap.Gram.Native6Phase16
public import ErdosOverlap.Gram.Native6Phase17
public import ErdosOverlap.Gram.Native6Phase18
public import ErdosOverlap.Gram.Native6Phase19
public import ErdosOverlap.Gram.Native6Phase20
public import ErdosOverlap.Gram.Native6Phase21
public import ErdosOverlap.Gram.Native6Phase22

/-!
# Every actual native6 phase row is physically valid

Each imported row includes ordinary kernel checks of its exact integer PSD
witness and complete raw multiplier assembly, followed by the analytic phase
theorem for an arbitrary admissible measurable partition.
-/

@[expose] public section

namespace ErdosOverlap.Gram

theorem native6_phase_functional {h : ℝ → ℝ} (hh : Admissible h)
    (row : PhaseFunctionalRow) (hr : row ∈ Native6Data.phaseRows) :
    (row.lowerAtZero : ℝ) + (row.meanCoefficient : ℝ) *
        profileMean (overlapProfile h)^2 ≤
      quartetFunctional h (phaseKernel row.cells row.gamma) := by
  simp only [Native6Data.phaseRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Native6Phase00.functional_lower_bound hh
  · exact Native6Phase01.functional_lower_bound hh
  · exact Native6Phase02.functional_lower_bound hh
  · exact Native6Phase03.functional_lower_bound hh
  · exact Native6Phase04.functional_lower_bound hh
  · exact Native6Phase05.functional_lower_bound hh
  · exact Native6Phase06.functional_lower_bound hh
  · exact Native6Phase07.functional_lower_bound hh
  · exact Native6Phase08.functional_lower_bound hh
  · exact Native6Phase09.functional_lower_bound hh
  · exact Native6Phase10.functional_lower_bound hh
  · exact Native6Phase11.functional_lower_bound hh
  · exact Native6Phase12.functional_lower_bound hh
  · exact Native6Phase13.functional_lower_bound hh
  · exact Native6Phase14.functional_lower_bound hh
  · exact Native6Phase15.functional_lower_bound hh
  · exact Native6Phase16.functional_lower_bound hh
  · exact Native6Phase17.functional_lower_bound hh
  · exact Native6Phase18.functional_lower_bound hh
  · exact Native6Phase19.functional_lower_bound hh
  · exact Native6Phase20.functional_lower_bound hh
  · exact Native6Phase21.functional_lower_bound hh
  · exact Native6Phase22.functional_lower_bound hh

end ErdosOverlap.Gram
