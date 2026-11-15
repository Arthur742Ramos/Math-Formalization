module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck070
public import ErdosOverlap.Certificate.Native6Grid.Coefficients08

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0560 :
    completeCoefficientRowCheck factorRow row0560 560 coefficients0560 = true := by
  have hlen : coefficients0560.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0560 oddDots0560
      641 560 0 coefficients0560 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0560_checked oddSum0560_checked hlen hs

theorem coefficientCheck0561 :
    completeCoefficientRowCheck factorRow row0561 561 coefficients0561 = true := by
  have hlen : coefficients0561.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0561 oddDots0561
      641 561 0 coefficients0561 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0561_checked oddSum0561_checked hlen hs

theorem coefficientCheck0562 :
    completeCoefficientRowCheck factorRow row0562 562 coefficients0562 = true := by
  have hlen : coefficients0562.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0562 oddDots0562
      641 562 0 coefficients0562 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0562_checked oddSum0562_checked hlen hs

theorem coefficientCheck0563 :
    completeCoefficientRowCheck factorRow row0563 563 coefficients0563 = true := by
  have hlen : coefficients0563.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0563 oddDots0563
      641 563 0 coefficients0563 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0563_checked oddSum0563_checked hlen hs

theorem coefficientCheck0564 :
    completeCoefficientRowCheck factorRow row0564 564 coefficients0564 = true := by
  have hlen : coefficients0564.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0564 oddDots0564
      641 564 0 coefficients0564 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0564_checked oddSum0564_checked hlen hs

theorem coefficientCheck0565 :
    completeCoefficientRowCheck factorRow row0565 565 coefficients0565 = true := by
  have hlen : coefficients0565.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0565 oddDots0565
      641 565 0 coefficients0565 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0565_checked oddSum0565_checked hlen hs

theorem coefficientCheck0566 :
    completeCoefficientRowCheck factorRow row0566 566 coefficients0566 = true := by
  have hlen : coefficients0566.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0566 oddDots0566
      641 566 0 coefficients0566 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0566_checked oddSum0566_checked hlen hs

theorem coefficientCheck0567 :
    completeCoefficientRowCheck factorRow row0567 567 coefficients0567 = true := by
  have hlen : coefficients0567.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0567 oddDots0567
      641 567 0 coefficients0567 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0567_checked oddSum0567_checked hlen hs


end
end ErdosOverlap.Native6Grid
