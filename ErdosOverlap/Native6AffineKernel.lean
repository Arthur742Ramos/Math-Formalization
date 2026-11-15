/-
Copyright (c) 2026. Released under the BSD-3-Clause license.
-/
module

public import ErdosOverlap.Certificate.Native6AffineData
public import ErdosOverlap.Certificate.Native6JumpData
public import ErdosOverlap.Native6Kernel

/-! # Exact equality of the frozen native6 kernel and its affine pieces -/

namespace ErdosOverlap.Native6Jumps
open MeasureTheory Set
public section
noncomputable section

/-- Every generated jump coefficient is linked to the original periodic
and phase rows.  This identity concerns real functions, not a sampled grid. -/
theorem finalJumps_source (t : ℝ) :
    affineJumpSum finalJumps t =
      affineJumpSum (periodicRowsJumps Native6Data.cells Native6Data.periodicRows) t +
      affineJumpSum (phaseRowsJumps Native6Data.phaseRows) t := by
  rw [finalJumps_value]
  simp only [componentBlocks, List.flatten_cons, List.flatten_nil, List.append_nil,
    affineJumpSum_append]
  rw [
    periodic00_value,
    periodic01_value,
    periodic02_value,
    periodic03_value,
    periodic04_value,
    periodic05_value,
    periodic06_value,
    periodic07_value,
    periodic08_value,
    periodic09_value,
    periodic10_value,
    periodic11_value,
    periodic12_value,
    periodic13_value,
    periodic14_value,
    periodic15_value,
    periodic16_value,
    periodic17_value,
    periodic18_value,
    periodic19_value,
    periodic20_value,
    periodic21_value,
    periodic22_value,
    periodic23_value,
    periodic24_value,
    periodic25_value,
    periodic26_value,
    periodic27_value,
    periodic28_value,
    periodic29_value,
    periodic30_value,
    periodic31_value,
    periodic32_value,
    periodic33_value,
    periodic34_value,
    periodic35_value,
    periodic36_value,
    periodic37_value,
    periodic38_value,
    periodic39_value,
    phase00_eq,
    phase01_eq,
    phase02_eq,
    phase03_eq,
    phase04_eq,
    phase05_eq,
    phase06_eq,
    phase07_eq,
    phase08_eq,
    phase09_eq,
    phase10_eq,
    phase11_eq,
    phase12_eq,
    phase13_eq,
    phase14_eq,
    phase15_eq,
    phase16_eq,
    phase17_eq,
    phase18_eq,
    phase19_eq,
    phase20_eq,
    phase21_eq,
    phase22_eq]
  have hempty : affineJumpSum [] t = 0 := rfl
  simp only [affineJumpSum_compressed, Native6Data.cells, Native6Data.periodicRows,
    Native6Data.phaseRows, periodicRowsJumps_append, phaseRowsJumps,
    affineJumpSum_append, hempty, add_zero, add_assoc]

/-- Exact equality away from the original periodic grid endpoints. -/
theorem kernel_eq_piece {p : AffinePiece} (hp : p ∈ pieces) {t : ℝ}
    (ht : t ∈ Ioo (p.left : ℝ) (p.right : ℝ))
    (hregular : GridRegular Native6Data.cells t) :
    Native6.kernel t = (Native6Data.y0 : ℝ) + (Native6Data.y2 : ℝ) * t^2 +
      Numerics.cosineSum Native6Trig.terms t + p.value t := by
  have hm := mem_pieces hp
  have hmem : p ∈ compileAffinePieces (-1) 3 0 0 finalJumps := by
    rw [← fullPieces_eq]
    exact hm.1
  have hv := compileAffinePieces_value (-1) 3 0 0 finalJumps finalJumps_sorted hmem ht
  simp only [Rat.cast_zero, zero_mul, zero_add] at hv
  rw [finalJumps_source,
    periodicRowsJumps_value (by decide +kernel : 0 < Native6Data.cells)
      Native6Data.periodicRows Native6Data.periodicRows_valid hregular,
    phaseRowsJumps_value Native6Data.phaseRows Native6Data.phaseRows_valid hregular.1.1.le] at hv
  unfold Native6.kernel
  linarith

/-- The discarded grid endpoints form a countable null set, so the
piece identity is sufficient for rigorous integration on every leaf. -/
theorem kernel_eq_piece_ae {p : AffinePiece} (hp : p ∈ pieces) :
    ∀ᵐ t : ℝ ∂volume.restrict (Ioo (p.left : ℝ) (p.right : ℝ)),
      Native6.kernel t = (Native6Data.y0 : ℝ) + (Native6Data.y2 : ℝ) * t^2 +
        Numerics.cosineSum Native6Trig.terms t + p.value t := by
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [ae_gridRegular Native6Data.cells] with t hregular ht
  have hm := mem_pieces hp
  have hl : (0 : ℝ) ≤ (p.left : ℝ) := by exact_mod_cast hm.2.1
  have hr : (p.right : ℝ) ≤ 2 := by exact_mod_cast hm.2.2
  exact kernel_eq_piece hp ht (hregular ⟨hl.trans_lt ht.1, ht.2.trans_le hr⟩)

end
end
end ErdosOverlap.Native6Jumps
