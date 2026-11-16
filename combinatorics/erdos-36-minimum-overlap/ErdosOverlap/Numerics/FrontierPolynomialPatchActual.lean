/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under the BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.NativePolynomialPatch
public import ErdosOverlap.Numerics.LeafIntegrationAE
public import ErdosOverlap.FrontierAffineKernel
public import ErdosOverlap.Numerics.FrontierPolynomial

/-!
# The actual native kernel is approximated by its checked polynomial patches

The only exceptional points come from the proved affine-piece identity.
The cosine error holds throughout the closed Taylor cell. Reflection uses
measure preservation, so the null exceptional set remains harmless for the
opposite half of the kernel as well.
-/

namespace ErdosOverlap.FrontierGrid

open Numerics MeasureTheory Set

public section

@[expose] def nativePolynomialPiece (j : ℕ) (p : AffinePiece) : PolynomialPiece :=
  affineKernelPatch (combinedCoefficients j)
    (taylorGridCenter j) taylorGridRadius FrontierData.y0 FrontierData.y2 p

theorem nativePolynomialPiece_error_ae {p : AffinePiece} (hp : p ∈ FrontierJumps.pieces)
    (j : ℕ) (hj : j < 1024) {l r : ℝ}
    (hpiece : Ioo l r ⊆ Ioo (p.left : ℝ) (p.right : ℝ))
    (hgrid : Ioo l r ⊆ Icc ((taylorGridCenter j : ℝ) - (taylorGridRadius : ℝ))
      ((taylorGridCenter j : ℝ) + (taylorGridRadius : ℝ))) :
    ∀ᵐ t ∂volume.restrict (Ioo l r),
      |Frontier.kernel t - (nativePolynomialPiece j p).value t| ≤
        (2 / 1000000000000 : ℝ) := by
  have hQ := (FrontierJumps.kernel_eq_piece_ae hp).filter_mono
    (ae_mono (Measure.restrict_mono hpiece le_rfl))
  have hC : ∀ᵐ t ∂volume.restrict (Ioo l r),
      |cosineSum FrontierTrig.terms t -
        polynomialValue (combinedCoefficients j)
          ((t - (taylorGridCenter j : ℝ)) / (taylorGridRadius : ℝ))| ≤
        (2 / 1000000000000 : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact combined_cosine_uniform_error_on_interval j hj (hgrid ht)
  exact affineKernelPatch_error_ae (combinedCoefficients j)
    (taylorGridCenter j) taylorGridRadius FrontierData.y0 FrontierData.y2 p
    (by norm_num [taylorGridRadius]) hQ hC

theorem nativePolynomialPiece_reflected_error_ae
    {p : AffinePiece} (hp : p ∈ FrontierJumps.pieces)
    (j : ℕ) (hj : j < 1024) {l r : ℝ}
    (hpiece : Ioo (2 - r) (2 - l) ⊆ Ioo (p.left : ℝ) (p.right : ℝ))
    (hgrid : Ioo (2 - r) (2 - l) ⊆
      Icc ((taylorGridCenter j : ℝ) - (taylorGridRadius : ℝ))
        ((taylorGridCenter j : ℝ) + (taylorGridRadius : ℝ))) :
    ∀ᵐ t ∂volume.restrict (Ioo l r),
      |Frontier.kernel (2 - t) - (nativePolynomialPiece j p).reflectTwo.value t| ≤
        (2 / 1000000000000 : ℝ) := by
  have h := ae_Ioo_comp_sub_left (nativePolynomialPiece_error_ae hp j hj hpiece hgrid) 2
  have hl : 2 - (2 - l) = l := by ring
  have hr : 2 - (2 - r) = r := by ring
  rw [hl, hr] at h
  filter_upwards [h] with t ht
  simpa only [PolynomialPiece.reflectTwo_value] using ht

/-- The executable leaf checker supplies rational endpoint comparisons.
These imply the set inclusions needed by the analytic patch theorem. -/
theorem nativePolynomialPieceAt_error_ae (i j : ℕ)
    (hi : i < 10463) (hj : j < 1024) (left right : ℚ)
    (hleft : (FrontierJumps.pieceAt i).left ≤ left)
    (hright : right ≤ (FrontierJumps.pieceAt i).right)
    (hgridLeft : taylorGridCenter j - taylorGridRadius ≤ left)
    (hgridRight : right ≤ taylorGridCenter j + taylorGridRadius) :
    ∀ᵐ t ∂volume.restrict (Ioo (left : ℝ) (right : ℝ)),
      |Frontier.kernel t -
        (nativePolynomialPiece j (FrontierJumps.pieceAt i)).value t| ≤
        (2 / 1000000000000 : ℝ) := by
  apply nativePolynomialPiece_error_ae (FrontierJumps.pieceAt_mem i hi) j hj
  · intro t ht
    exact ⟨lt_of_le_of_lt (by exact_mod_cast hleft) ht.1,
      lt_of_lt_of_le ht.2 (by exact_mod_cast hright)⟩
  · intro t ht
    have hl : (taylorGridCenter j : ℝ) - (taylorGridRadius : ℝ) ≤ (left : ℝ) := by
      exact_mod_cast hgridLeft
    have hr : (right : ℝ) ≤ (taylorGridCenter j : ℝ) + (taylorGridRadius : ℝ) := by
      exact_mod_cast hgridRight
    exact ⟨hl.trans ht.1.le, ht.2.le.trans hr⟩

/-- The corresponding reflected leaf uses the same rational comparisons,
with endpoints `2-right` and `2-left`. -/
theorem nativePolynomialPieceAt_reflected_error_ae (i j : ℕ)
    (hi : i < 10463) (hj : j < 1024) (left right : ℚ)
    (hleft : (FrontierJumps.pieceAt i).left ≤ 2 - right)
    (hright : 2 - left ≤ (FrontierJumps.pieceAt i).right)
    (hgridLeft : taylorGridCenter j - taylorGridRadius ≤ 2 - right)
    (hgridRight : 2 - left ≤ taylorGridCenter j + taylorGridRadius) :
    ∀ᵐ t ∂volume.restrict (Ioo (left : ℝ) (right : ℝ)),
      |Frontier.kernel (2 - t) -
        (nativePolynomialPiece j (FrontierJumps.pieceAt i)).reflectTwo.value t| ≤
        (2 / 1000000000000 : ℝ) := by
  apply nativePolynomialPiece_reflected_error_ae (FrontierJumps.pieceAt_mem i hi) j hj
  · intro t ht
    exact ⟨lt_of_le_of_lt (by exact_mod_cast hleft) ht.1,
      lt_of_lt_of_le ht.2 (by exact_mod_cast hright)⟩
  · intro t ht
    have hl : (taylorGridCenter j : ℝ) - (taylorGridRadius : ℝ) ≤ 2 - (right : ℝ) := by
      exact_mod_cast hgridLeft
    have hr : 2 - (left : ℝ) ≤ (taylorGridCenter j : ℝ) + (taylorGridRadius : ℝ) := by
      exact_mod_cast hgridRight
    exact ⟨hl.trans ht.1.le, ht.2.le.trans hr⟩

end
end ErdosOverlap.FrontierGrid
