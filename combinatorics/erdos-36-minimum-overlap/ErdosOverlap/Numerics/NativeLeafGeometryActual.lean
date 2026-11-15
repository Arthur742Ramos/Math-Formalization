/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.NativeLeafGeometry
public import ErdosOverlap.Numerics.NativePolynomialPatchActual

/-!
# Actual kernel approximation on a checked integration leaf

The geometry checker establishes rational inclusions in both affine pieces
and both Taylor cells.  The analytic conclusion below is therefore about
the original native kernel, including its reflected argument.
-/

namespace ErdosOverlap.Native6Leaves

open Numerics MeasureTheory Set

public section

theorem Geometry.patchA_error_ae {g : Geometry} (hg : g.Valid) :
    ∀ᵐ t ∂volume.restrict (Ioo (g.left : ℝ) (g.right : ℝ)),
      |Native6.kernel t - g.patchA.value t| ≤ (1 / 1000000000000 : ℝ) := by
  rcases hg with ⟨_, _, _, hpA, _, hj, hAL, hAR, _, _, hjL, hjR, _, _⟩
  simpa only [Geometry.patchA, Native6Grid.nativePolynomialPiece] using
    Native6Grid.nativePolynomialPieceAt_error_ae g.pieceA g.grid hpA (by omega)
      g.left g.right hAL hAR hjL hjR

theorem Geometry.patchB_error_ae {g : Geometry} (hg : g.Valid) :
    ∀ᵐ t ∂volume.restrict (Ioo (g.left : ℝ) (g.right : ℝ)),
      |Native6.kernel (2 - t) - g.patchB.value t| ≤ (1 / 1000000000000 : ℝ) := by
  rcases hg with ⟨_, _, _, _, hpB, _, _, _, hBL, hBR, _, _, hjL, hjR⟩
  simpa only [Geometry.patchB, Native6Grid.nativePolynomialPiece] using
    Native6Grid.nativePolynomialPieceAt_reflected_error_ae g.pieceB (1023 - g.grid)
      hpB (by omega) g.left g.right hBL hBR hjL hjR

theorem Geometry.check_approximation {g : Geometry} (hg : g.check = true) :
    (∀ᵐ t ∂volume.restrict (Ioo (g.left : ℝ) (g.right : ℝ)),
      |Native6.kernel t - g.patchA.value t| ≤ (1 / 1000000000000 : ℝ)) ∧
    (∀ᵐ t ∂volume.restrict (Ioo (g.left : ℝ) (g.right : ℝ)),
      |Native6.kernel (2 - t) - g.patchB.value t| ≤ (1 / 1000000000000 : ℝ)) :=
  ⟨Geometry.patchA_error_ae (Geometry.check_valid hg),
    Geometry.patchB_error_ae (Geometry.check_valid hg)⟩

end
end ErdosOverlap.Native6Leaves
