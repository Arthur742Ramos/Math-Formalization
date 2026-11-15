module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck049
public import ErdosOverlap.Certificate.Native6Grid.Coefficients06

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0392 :
    completeCoefficientRowCheck factorRow row0392 392 coefficients0392 = true := by
  have hlen : coefficients0392.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0392 oddDots0392
      641 392 0 coefficients0392 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0392_checked oddSum0392_checked hlen hs

theorem coefficientCheck0393 :
    completeCoefficientRowCheck factorRow row0393 393 coefficients0393 = true := by
  have hlen : coefficients0393.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0393 oddDots0393
      641 393 0 coefficients0393 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0393_checked oddSum0393_checked hlen hs

theorem coefficientCheck0394 :
    completeCoefficientRowCheck factorRow row0394 394 coefficients0394 = true := by
  have hlen : coefficients0394.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0394 oddDots0394
      641 394 0 coefficients0394 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0394_checked oddSum0394_checked hlen hs

theorem coefficientCheck0395 :
    completeCoefficientRowCheck factorRow row0395 395 coefficients0395 = true := by
  have hlen : coefficients0395.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0395 oddDots0395
      641 395 0 coefficients0395 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0395_checked oddSum0395_checked hlen hs

theorem coefficientCheck0396 :
    completeCoefficientRowCheck factorRow row0396 396 coefficients0396 = true := by
  have hlen : coefficients0396.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0396 oddDots0396
      641 396 0 coefficients0396 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0396_checked oddSum0396_checked hlen hs

theorem coefficientCheck0397 :
    completeCoefficientRowCheck factorRow row0397 397 coefficients0397 = true := by
  have hlen : coefficients0397.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0397 oddDots0397
      641 397 0 coefficients0397 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0397_checked oddSum0397_checked hlen hs

theorem coefficientCheck0398 :
    completeCoefficientRowCheck factorRow row0398 398 coefficients0398 = true := by
  have hlen : coefficients0398.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0398 oddDots0398
      641 398 0 coefficients0398 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0398_checked oddSum0398_checked hlen hs

theorem coefficientCheck0399 :
    completeCoefficientRowCheck factorRow row0399 399 coefficients0399 = true := by
  have hlen : coefficients0399.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0399 oddDots0399
      641 399 0 coefficients0399 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0399_checked oddSum0399_checked hlen hs


end
end ErdosOverlap.Native6Grid
