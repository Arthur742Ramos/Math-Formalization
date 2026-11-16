module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck053
public import ErdosOverlap.Certificate.Native6Grid.Coefficients06

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0424 :
    completeCoefficientRowCheck factorRow row0424 424 coefficients0424 = true := by
  have hlen : coefficients0424.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0424 oddDots0424
      641 424 0 coefficients0424 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0424_checked oddSum0424_checked hlen hs

theorem coefficientCheck0425 :
    completeCoefficientRowCheck factorRow row0425 425 coefficients0425 = true := by
  have hlen : coefficients0425.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0425 oddDots0425
      641 425 0 coefficients0425 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0425_checked oddSum0425_checked hlen hs

theorem coefficientCheck0426 :
    completeCoefficientRowCheck factorRow row0426 426 coefficients0426 = true := by
  have hlen : coefficients0426.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0426 oddDots0426
      641 426 0 coefficients0426 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0426_checked oddSum0426_checked hlen hs

theorem coefficientCheck0427 :
    completeCoefficientRowCheck factorRow row0427 427 coefficients0427 = true := by
  have hlen : coefficients0427.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0427 oddDots0427
      641 427 0 coefficients0427 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0427_checked oddSum0427_checked hlen hs

theorem coefficientCheck0428 :
    completeCoefficientRowCheck factorRow row0428 428 coefficients0428 = true := by
  have hlen : coefficients0428.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0428 oddDots0428
      641 428 0 coefficients0428 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0428_checked oddSum0428_checked hlen hs

theorem coefficientCheck0429 :
    completeCoefficientRowCheck factorRow row0429 429 coefficients0429 = true := by
  have hlen : coefficients0429.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0429 oddDots0429
      641 429 0 coefficients0429 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0429_checked oddSum0429_checked hlen hs

theorem coefficientCheck0430 :
    completeCoefficientRowCheck factorRow row0430 430 coefficients0430 = true := by
  have hlen : coefficients0430.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0430 oddDots0430
      641 430 0 coefficients0430 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0430_checked oddSum0430_checked hlen hs

theorem coefficientCheck0431 :
    completeCoefficientRowCheck factorRow row0431 431 coefficients0431 = true := by
  have hlen : coefficients0431.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0431 oddDots0431
      641 431 0 coefficients0431 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0431_checked oddSum0431_checked hlen hs


end
end ErdosOverlap.Native6Grid
