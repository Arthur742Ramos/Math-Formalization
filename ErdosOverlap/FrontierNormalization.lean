/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.FrontierKernel
public import ErdosOverlap.Certificate.FrontierTrigIdentities
public import ErdosOverlap.Certificate.Native6Grid.SincChecks

namespace ErdosOverlap.Frontier
open Numerics
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def lowerAtZeroBound : ℚ := (99999999999999 / 100000000000000 : ℚ)
def sincCorrectionLower : ℚ := (-1477614389113330945402094432448410984192410151803347471817058069 / 1771458580717425000000000000000000000000000000000000000000000000000000 : ℚ)

theorem sinc_correction_checked :
    (sincSumBox FrontierTrig.correctionTerms).lowerBoundedBy sincCorrectionLower = true := by
  decide +kernel

theorem normalization_identity : lowerAtZeroBound =
    Native6Grid.checkedLowerAtZero +
      (FrontierData.rationalPartExact - Native6.rationalPartExact) + sincCorrectionLower := by
  decide +kernel

theorem lowerAtZeroBound_le : (lowerAtZeroBound : ℝ) ≤ lowerAtZero := by
  have hold := Native6Grid.lowerAtZero_checked
  have hcorrection := sincSum_lower_of_check _ _ sinc_correction_checked
  rw [Native6.lowerAtZero_decomposition] at hold
  have hid : (lowerAtZeroBound : ℝ) = (Native6Grid.checkedLowerAtZero : ℝ) +
      ((FrontierData.rationalPartExact : ℝ) - (Native6.rationalPartExact : ℝ)) +
      (sincCorrectionLower : ℝ) := by
    exact_mod_cast normalization_identity
  rw [hid, lowerAtZero, FrontierTrig.lower_eq_old_add_corrections]
  linarith

end
end ErdosOverlap.Frontier
