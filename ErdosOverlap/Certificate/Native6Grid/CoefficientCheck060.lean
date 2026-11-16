module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck060
public import ErdosOverlap.Certificate.Native6Grid.Coefficients07

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0480 :
    completeCoefficientRowCheck factorRow row0480 480 coefficients0480 = true := by
  have hlen : coefficients0480.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0480 oddDots0480
      641 480 0 coefficients0480 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0480_checked oddSum0480_checked hlen hs

theorem coefficientCheck0481 :
    completeCoefficientRowCheck factorRow row0481 481 coefficients0481 = true := by
  have hlen : coefficients0481.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0481 oddDots0481
      641 481 0 coefficients0481 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0481_checked oddSum0481_checked hlen hs

theorem coefficientCheck0482 :
    completeCoefficientRowCheck factorRow row0482 482 coefficients0482 = true := by
  have hlen : coefficients0482.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0482 oddDots0482
      641 482 0 coefficients0482 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0482_checked oddSum0482_checked hlen hs

theorem coefficientCheck0483 :
    completeCoefficientRowCheck factorRow row0483 483 coefficients0483 = true := by
  have hlen : coefficients0483.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0483 oddDots0483
      641 483 0 coefficients0483 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0483_checked oddSum0483_checked hlen hs

theorem coefficientCheck0484 :
    completeCoefficientRowCheck factorRow row0484 484 coefficients0484 = true := by
  have hlen : coefficients0484.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0484 oddDots0484
      641 484 0 coefficients0484 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0484_checked oddSum0484_checked hlen hs

theorem coefficientCheck0485 :
    completeCoefficientRowCheck factorRow row0485 485 coefficients0485 = true := by
  have hlen : coefficients0485.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0485 oddDots0485
      641 485 0 coefficients0485 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0485_checked oddSum0485_checked hlen hs

theorem coefficientCheck0486 :
    completeCoefficientRowCheck factorRow row0486 486 coefficients0486 = true := by
  have hlen : coefficients0486.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0486 oddDots0486
      641 486 0 coefficients0486 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0486_checked oddSum0486_checked hlen hs

theorem coefficientCheck0487 :
    completeCoefficientRowCheck factorRow row0487 487 coefficients0487 = true := by
  have hlen : coefficients0487.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0487 oddDots0487
      641 487 0 coefficients0487 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0487_checked oddSum0487_checked hlen hs


end
end ErdosOverlap.Native6Grid
