module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck062
public import ErdosOverlap.Certificate.Native6Grid.Coefficients07

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0496 :
    completeCoefficientRowCheck factorRow row0496 496 coefficients0496 = true := by
  have hlen : coefficients0496.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0496 oddDots0496
      641 496 0 coefficients0496 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0496_checked oddSum0496_checked hlen hs

theorem coefficientCheck0497 :
    completeCoefficientRowCheck factorRow row0497 497 coefficients0497 = true := by
  have hlen : coefficients0497.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0497 oddDots0497
      641 497 0 coefficients0497 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0497_checked oddSum0497_checked hlen hs

theorem coefficientCheck0498 :
    completeCoefficientRowCheck factorRow row0498 498 coefficients0498 = true := by
  have hlen : coefficients0498.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0498 oddDots0498
      641 498 0 coefficients0498 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0498_checked oddSum0498_checked hlen hs

theorem coefficientCheck0499 :
    completeCoefficientRowCheck factorRow row0499 499 coefficients0499 = true := by
  have hlen : coefficients0499.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0499 oddDots0499
      641 499 0 coefficients0499 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0499_checked oddSum0499_checked hlen hs

theorem coefficientCheck0500 :
    completeCoefficientRowCheck factorRow row0500 500 coefficients0500 = true := by
  have hlen : coefficients0500.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0500 oddDots0500
      641 500 0 coefficients0500 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0500_checked oddSum0500_checked hlen hs

theorem coefficientCheck0501 :
    completeCoefficientRowCheck factorRow row0501 501 coefficients0501 = true := by
  have hlen : coefficients0501.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0501 oddDots0501
      641 501 0 coefficients0501 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0501_checked oddSum0501_checked hlen hs

theorem coefficientCheck0502 :
    completeCoefficientRowCheck factorRow row0502 502 coefficients0502 = true := by
  have hlen : coefficients0502.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0502 oddDots0502
      641 502 0 coefficients0502 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0502_checked oddSum0502_checked hlen hs

theorem coefficientCheck0503 :
    completeCoefficientRowCheck factorRow row0503 503 coefficients0503 = true := by
  have hlen : coefficients0503.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0503 oddDots0503
      641 503 0 coefficients0503 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0503_checked oddSum0503_checked hlen hs


end
end ErdosOverlap.Native6Grid
