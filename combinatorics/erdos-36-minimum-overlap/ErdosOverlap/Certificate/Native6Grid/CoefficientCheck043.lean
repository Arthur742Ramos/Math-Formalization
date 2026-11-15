module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck043
public import ErdosOverlap.Certificate.Native6Grid.Coefficients05

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0344 :
    completeCoefficientRowCheck factorRow row0344 344 coefficients0344 = true := by
  have hlen : coefficients0344.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0344 oddDots0344
      641 344 0 coefficients0344 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0344_checked oddSum0344_checked hlen hs

theorem coefficientCheck0345 :
    completeCoefficientRowCheck factorRow row0345 345 coefficients0345 = true := by
  have hlen : coefficients0345.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0345 oddDots0345
      641 345 0 coefficients0345 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0345_checked oddSum0345_checked hlen hs

theorem coefficientCheck0346 :
    completeCoefficientRowCheck factorRow row0346 346 coefficients0346 = true := by
  have hlen : coefficients0346.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0346 oddDots0346
      641 346 0 coefficients0346 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0346_checked oddSum0346_checked hlen hs

theorem coefficientCheck0347 :
    completeCoefficientRowCheck factorRow row0347 347 coefficients0347 = true := by
  have hlen : coefficients0347.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0347 oddDots0347
      641 347 0 coefficients0347 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0347_checked oddSum0347_checked hlen hs

theorem coefficientCheck0348 :
    completeCoefficientRowCheck factorRow row0348 348 coefficients0348 = true := by
  have hlen : coefficients0348.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0348 oddDots0348
      641 348 0 coefficients0348 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0348_checked oddSum0348_checked hlen hs

theorem coefficientCheck0349 :
    completeCoefficientRowCheck factorRow row0349 349 coefficients0349 = true := by
  have hlen : coefficients0349.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0349 oddDots0349
      641 349 0 coefficients0349 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0349_checked oddSum0349_checked hlen hs

theorem coefficientCheck0350 :
    completeCoefficientRowCheck factorRow row0350 350 coefficients0350 = true := by
  have hlen : coefficients0350.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0350 oddDots0350
      641 350 0 coefficients0350 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0350_checked oddSum0350_checked hlen hs

theorem coefficientCheck0351 :
    completeCoefficientRowCheck factorRow row0351 351 coefficients0351 = true := by
  have hlen : coefficients0351.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0351 oddDots0351
      641 351 0 coefficients0351 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0351_checked oddSum0351_checked hlen hs


end
end ErdosOverlap.Native6Grid
