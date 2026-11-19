/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Numerics.FrontierLeafCertificate
public import ErdosOverlap.Numerics.FrontierLeafGeometryActual

/-!
# Actual native integral leaves with every approximation premise discharged

The geometric polynomial approximation is supplied by the proved exact
native affine compiler and uniform Taylor error theorem.
-/

@[expose] public section

namespace ErdosOverlap.FrontierLeaves

open Numerics MeasureTheory Set

theorem CheckedGeometry.approximation (g : CheckedGeometry) : g.val.Approximation := by
  simpa only [Geometry.Approximation, approximationError, Rat.cast_div,
    Rat.cast_one, Rat.cast_ofNat] using Geometry.check_approximation g.property

theorem CheckedProfileLeaf.sound {mode : Fin 20} (leaf : CheckedProfileLeaf mode) :
    (leaf.val.lowerBound : ℝ) ≤
      ∫ t in (leaf.val.geometry.val.left : ℝ)..(leaf.val.geometry.val.right : ℝ),
        profileIntegrand mode t :=
  leaf.val.sound mode leaf.property leaf.val.geometry.approximation

theorem CheckedCentralLeaf.sound (leaf : CheckedCentralLeaf) :
    (leaf.val.lowerBound : ℝ) ≤
      ∫ t in (leaf.val.geometry.val.left : ℝ)..(leaf.val.geometry.val.right : ℝ), centralIntegrand t :=
  leaf.val.sound leaf.property leaf.val.geometry.approximation

theorem CheckedDenominatorLeaf.sound (leaf : CheckedDenominatorLeaf) :
    (∫ t in (leaf.val.geometry.val.left : ℝ)..(leaf.val.geometry.val.right : ℝ), denominatorIntegrand t) ≤
      (leaf.val.upperBound : ℝ) :=
  leaf.val.sound leaf.property leaf.val.geometry.approximation

theorem integral_denominatorIntegrand :
    (∫ t in (0 : ℝ)..1, denominatorIntegrand t) = kernelDenominator Frontier.kernel := by
  simp only [denominatorIntegrand, kernelDenominator, intervalIntegral.integral_const_mul]

theorem integral_centralIntegrand :
    (∫ t in (0 : ℝ)..1, centralIntegrand t) =
      ∫ t in (0 : ℝ)..1,
        kernelConjugate Frontier.kernel (auxiliaryLevel : ℝ) (boxCap : ℝ) 0 (fun _ => 0) t := by
  simp only [kernelConjugate_zero_witness, centralIntegrand]

end ErdosOverlap.FrontierLeaves
