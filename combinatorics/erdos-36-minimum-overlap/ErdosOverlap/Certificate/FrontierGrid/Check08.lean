/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.FrontierGrid.Factors
public import ErdosOverlap.Certificate.FrontierGrid.Rows

namespace ErdosOverlap.FrontierGrid
open Numerics
@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem coefficients_chunk08 (j : ℕ) (hlo : 128 ≤ j) (hhi : j < 144) :
    completeCoefficientRowCheck factors (stateRow j) j (coefficientRow j) = true := by
  interval_cases j <;> decide +kernel

theorem transitions_chunk08 (j : ℕ) (hj : j+1 < 1024)
    (hlo : 128 ≤ j) (hhi : j < 144) :
    transitionRowCheck seeds (stateRow j) (stateRow (j+1)) = true := by
  have hj' : j < 1023 := by omega
  interval_cases j <;> decide +kernel

end
end ErdosOverlap.FrontierGrid
