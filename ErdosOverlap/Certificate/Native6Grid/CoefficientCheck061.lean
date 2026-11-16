module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck061
public import ErdosOverlap.Certificate.Native6Grid.Coefficients07

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0488 :
    completeCoefficientRowCheck factorRow row0488 488 coefficients0488 = true := by
  have hlen : coefficients0488.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0488 oddDots0488
      641 488 0 coefficients0488 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0488_checked oddSum0488_checked hlen hs

theorem coefficientCheck0489 :
    completeCoefficientRowCheck factorRow row0489 489 coefficients0489 = true := by
  have hlen : coefficients0489.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0489 oddDots0489
      641 489 0 coefficients0489 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0489_checked oddSum0489_checked hlen hs

theorem coefficientCheck0490 :
    completeCoefficientRowCheck factorRow row0490 490 coefficients0490 = true := by
  have hlen : coefficients0490.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0490 oddDots0490
      641 490 0 coefficients0490 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0490_checked oddSum0490_checked hlen hs

theorem coefficientCheck0491 :
    completeCoefficientRowCheck factorRow row0491 491 coefficients0491 = true := by
  have hlen : coefficients0491.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0491 oddDots0491
      641 491 0 coefficients0491 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0491_checked oddSum0491_checked hlen hs

theorem coefficientCheck0492 :
    completeCoefficientRowCheck factorRow row0492 492 coefficients0492 = true := by
  have hlen : coefficients0492.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0492 oddDots0492
      641 492 0 coefficients0492 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0492_checked oddSum0492_checked hlen hs

theorem coefficientCheck0493 :
    completeCoefficientRowCheck factorRow row0493 493 coefficients0493 = true := by
  have hlen : coefficients0493.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0493 oddDots0493
      641 493 0 coefficients0493 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0493_checked oddSum0493_checked hlen hs

theorem coefficientCheck0494 :
    completeCoefficientRowCheck factorRow row0494 494 coefficients0494 = true := by
  have hlen : coefficients0494.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0494 oddDots0494
      641 494 0 coefficients0494 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0494_checked oddSum0494_checked hlen hs

theorem coefficientCheck0495 :
    completeCoefficientRowCheck factorRow row0495 495 coefficients0495 = true := by
  have hlen : coefficients0495.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0495 oddDots0495
      641 495 0 coefficients0495 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0495_checked oddSum0495_checked hlen hs


end
end ErdosOverlap.Native6Grid
