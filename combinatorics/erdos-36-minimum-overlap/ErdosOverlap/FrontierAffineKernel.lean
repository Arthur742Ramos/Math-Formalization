/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.FrontierAffineData
public import ErdosOverlap.FrontierKernel

namespace ErdosOverlap.FrontierJumps
open MeasureTheory Set
public section
noncomputable section

/-- Exact equality away from the original periodic grid endpoints. -/
theorem kernel_eq_piece {p : AffinePiece} (hp : p ∈ pieces) {t : ℝ}
    (ht : t ∈ Ioo (p.left : ℝ) (p.right : ℝ))
    (hregular : GridRegular Native6Data.cells t) :
    Frontier.kernel t = (FrontierData.y0 : ℝ) + (FrontierData.y2 : ℝ) * t^2 +
      Numerics.cosineSum FrontierTrig.terms t + p.value t := by
  have hm := mem_pieces hp
  have hmem : p ∈ compileAffinePieces (-1) 3 0 0 finalJumps := by
    rw [← fullPieces_eq]
    exact hm.1
  have hv := compileAffinePieces_value (-1) 3 0 0 finalJumps finalJumps_sorted hmem ht
  simp only [Rat.cast_zero, zero_mul, zero_add] at hv
  rw [finalJumps_source,
    periodicRowsJumps_value (by decide +kernel : 0 < Native6Data.cells)
      FrontierData.periodicRows FrontierData.periodicRows_valid hregular,
    phaseRowsJumps_value FrontierData.phaseRows FrontierData.phaseRows_valid hregular.1.1.le] at hv
  unfold Frontier.kernel
  linarith

/-- The discarded grid endpoints form a countable null set, so the
piece identity is sufficient for rigorous integration on every leaf. -/
theorem kernel_eq_piece_ae {p : AffinePiece} (hp : p ∈ pieces) :
    ∀ᵐ t : ℝ ∂volume.restrict (Ioo (p.left : ℝ) (p.right : ℝ)),
      Frontier.kernel t = (FrontierData.y0 : ℝ) + (FrontierData.y2 : ℝ) * t^2 +
        Numerics.cosineSum FrontierTrig.terms t + p.value t := by
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [ae_gridRegular Native6Data.cells] with t hregular ht
  have hm := mem_pieces hp
  have hl : (0 : ℝ) ≤ (p.left : ℝ) := by exact_mod_cast hm.2.1
  have hr : (p.right : ℝ) ≤ 2 := by exact_mod_cast hm.2.2
  exact kernel_eq_piece hp ht (hregular ⟨hl.trans_lt ht.1, ht.2.trans_le hr⟩)

end
end
end ErdosOverlap.FrontierJumps
