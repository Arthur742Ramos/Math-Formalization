/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.FrontierPolynomialCache

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section

def sourcePatchConstant (piece grid : ℕ) : ℚ :=
  let center := taylorGridCenter grid
  let affine := FrontierJumps.pieceAt piece
  (FrontierGrid.combinedCoefficients grid).getD 0 0 +
    (FrontierData.y0 + affine.constant + affine.linear * center + FrontierData.y2 * center ^ 2)

def sourcePatchLinear (piece grid : ℕ) : ℚ :=
  let center := taylorGridCenter grid
  let affine := FrontierJumps.pieceAt piece
  (FrontierGrid.combinedCoefficients grid).getD 1 0 +
    taylorGridRadius * (affine.linear + 2 * FrontierData.y2 * center)

/-- The quadratic coefficient and every higher coefficient depend only on the grid. -/
def sourcePatchSuffix (grid : ℕ) : List ℚ :=
  let coefficients := FrontierGrid.combinedCoefficients grid
  (coefficients.getD 2 0 + FrontierData.y2 * taylorGridRadius ^ 2) :: coefficients.drop 3

theorem sourcePatchCoefficients_eq (piece grid : ℕ) :
    (sourcePatch piece grid).coefficients =
      sourcePatchConstant piece grid :: sourcePatchLinear piece grid :: sourcePatchSuffix grid := rfl

def checkPatchSuffix (tail : PolynomialBoxCache) (grid : ℕ) : Bool :=
  let cs := sourcePatchSuffix grid
  decide (tail.coefficients = cs.map FixedBox.ofRat ∧
    tail.primitive = (primitiveTail 2 cs).map FixedBox.ofRat ∧
    tail.weightedPrimitive = (primitiveTail 3 cs).map FixedBox.ofRat)

def CheckedPatchSuffix (grid : ℕ) :=
  { tail : PolynomialBoxCache // checkPatchSuffix tail grid = true }

structure PatchPrefixBoxes where
  constant : FixedBox
  linear : FixedBox
  primitiveConstant : FixedBox
  primitiveLinear : FixedBox
  weightedConstant : FixedBox
  weightedLinear : FixedBox

def PatchPrefixBoxes.check (head : PatchPrefixBoxes) (c0 c1 : ℚ) : Bool :=
  decide (head.constant = FixedBox.ofRat c0 ∧ head.linear = FixedBox.ofRat c1 ∧
    head.primitiveConstant = FixedBox.ofRat (c0 / 1) ∧ head.primitiveLinear = FixedBox.ofRat (c1 / 2) ∧
    head.weightedConstant = FixedBox.ofRat (c0 / 2) ∧ head.weightedLinear = FixedBox.ofRat (c1 / 3))

def PatchPrefixBoxes.prepend (head : PatchPrefixBoxes) (tail : PolynomialBoxCache) : PolynomialBoxCache :=
  ⟨head.constant :: head.linear :: tail.coefficients,
    ⟨0, 0⟩ :: head.primitiveConstant :: head.primitiveLinear :: tail.primitive,
    ⟨0, 0⟩ :: ⟨0, 0⟩ :: head.weightedConstant :: head.weightedLinear :: tail.weightedPrimitive⟩

theorem patchBoxCheck_of_parts {head : PatchPrefixBoxes} {tail : PolynomialBoxCache}
    {piece grid : ℕ}
    (headCheck : head.check (sourcePatchConstant piece grid) (sourcePatchLinear piece grid) = true)
    (tailCheck : checkPatchSuffix tail grid = true) :
    (head.prepend tail).check (sourcePatch piece grid) = true := by
  simp only [PatchPrefixBoxes.check, decide_eq_true_eq] at headCheck
  simp only [checkPatchSuffix, decide_eq_true_eq] at tailCheck
  obtain ⟨hc, hl, hpc, hpl, hwc, hwl⟩ := headCheck
  obtain ⟨ht, hp, hw⟩ := tailCheck
  have hz : (⟨0, 0⟩ : FixedBox) = FixedBox.ofRat 0 := by decide +kernel
  simp only [PolynomialBoxCache.check, decide_eq_true_eq, PatchPrefixBoxes.prepend, sourcePatchCoefficients_eq,
    primitiveCoeffs, weightedPrimitiveCoeffs, primitiveTail, List.map_cons]
  refine ⟨?_, ?_, ?_⟩
  · rw [hc, hl, ht]
  · rw [hz, hpc, hpl, hp]
    norm_num
  · rw [hz, hwc, hwl, hw]
    norm_num

def checkedPatchOfParts (piece grid : ℕ) (head : PatchPrefixBoxes) (tail : CheckedPatchSuffix grid)
    (headCheck : head.check (sourcePatchConstant piece grid) (sourcePatchLinear piece grid) = true) :
    CheckedPatchCache piece grid :=
  ⟨head.prepend tail.val, patchBoxCheck_of_parts headCheck tail.property⟩

end
end ErdosOverlap.FrontierLeaves
