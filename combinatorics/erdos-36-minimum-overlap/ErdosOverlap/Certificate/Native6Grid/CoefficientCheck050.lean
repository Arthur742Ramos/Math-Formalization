module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck050
public import ErdosOverlap.Certificate.Native6Grid.Coefficients06

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0400 :
    completeCoefficientRowCheck factorRow row0400 400 coefficients0400 = true := by
  have hlen : coefficients0400.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0400 oddDots0400
      641 400 0 coefficients0400 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0400_checked oddSum0400_checked hlen hs

theorem coefficientCheck0401 :
    completeCoefficientRowCheck factorRow row0401 401 coefficients0401 = true := by
  have hlen : coefficients0401.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0401 oddDots0401
      641 401 0 coefficients0401 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0401_checked oddSum0401_checked hlen hs

theorem coefficientCheck0402 :
    completeCoefficientRowCheck factorRow row0402 402 coefficients0402 = true := by
  have hlen : coefficients0402.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0402 oddDots0402
      641 402 0 coefficients0402 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0402_checked oddSum0402_checked hlen hs

theorem coefficientCheck0403 :
    completeCoefficientRowCheck factorRow row0403 403 coefficients0403 = true := by
  have hlen : coefficients0403.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0403 oddDots0403
      641 403 0 coefficients0403 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0403_checked oddSum0403_checked hlen hs

theorem coefficientCheck0404 :
    completeCoefficientRowCheck factorRow row0404 404 coefficients0404 = true := by
  have hlen : coefficients0404.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0404 oddDots0404
      641 404 0 coefficients0404 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0404_checked oddSum0404_checked hlen hs

theorem coefficientCheck0405 :
    completeCoefficientRowCheck factorRow row0405 405 coefficients0405 = true := by
  have hlen : coefficients0405.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0405 oddDots0405
      641 405 0 coefficients0405 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0405_checked oddSum0405_checked hlen hs

theorem coefficientCheck0406 :
    completeCoefficientRowCheck factorRow row0406 406 coefficients0406 = true := by
  have hlen : coefficients0406.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0406 oddDots0406
      641 406 0 coefficients0406 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0406_checked oddSum0406_checked hlen hs

theorem coefficientCheck0407 :
    completeCoefficientRowCheck factorRow row0407 407 coefficients0407 = true := by
  have hlen : coefficients0407.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0407 oddDots0407
      641 407 0 coefficients0407 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0407_checked oddSum0407_checked hlen hs


end
end ErdosOverlap.Native6Grid
