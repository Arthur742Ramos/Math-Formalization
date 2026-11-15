module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck035
public import ErdosOverlap.Certificate.Native6Grid.Coefficients04

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0280 :
    completeCoefficientRowCheck factorRow row0280 280 coefficients0280 = true := by
  have hlen : coefficients0280.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0280 oddDots0280
      641 280 0 coefficients0280 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0280_checked oddSum0280_checked hlen hs

theorem coefficientCheck0281 :
    completeCoefficientRowCheck factorRow row0281 281 coefficients0281 = true := by
  have hlen : coefficients0281.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0281 oddDots0281
      641 281 0 coefficients0281 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0281_checked oddSum0281_checked hlen hs

theorem coefficientCheck0282 :
    completeCoefficientRowCheck factorRow row0282 282 coefficients0282 = true := by
  have hlen : coefficients0282.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0282 oddDots0282
      641 282 0 coefficients0282 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0282_checked oddSum0282_checked hlen hs

theorem coefficientCheck0283 :
    completeCoefficientRowCheck factorRow row0283 283 coefficients0283 = true := by
  have hlen : coefficients0283.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0283 oddDots0283
      641 283 0 coefficients0283 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0283_checked oddSum0283_checked hlen hs

theorem coefficientCheck0284 :
    completeCoefficientRowCheck factorRow row0284 284 coefficients0284 = true := by
  have hlen : coefficients0284.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0284 oddDots0284
      641 284 0 coefficients0284 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0284_checked oddSum0284_checked hlen hs

theorem coefficientCheck0285 :
    completeCoefficientRowCheck factorRow row0285 285 coefficients0285 = true := by
  have hlen : coefficients0285.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0285 oddDots0285
      641 285 0 coefficients0285 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0285_checked oddSum0285_checked hlen hs

theorem coefficientCheck0286 :
    completeCoefficientRowCheck factorRow row0286 286 coefficients0286 = true := by
  have hlen : coefficients0286.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0286 oddDots0286
      641 286 0 coefficients0286 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0286_checked oddSum0286_checked hlen hs

theorem coefficientCheck0287 :
    completeCoefficientRowCheck factorRow row0287 287 coefficients0287 = true := by
  have hlen : coefficients0287.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0287 oddDots0287
      641 287 0 coefficients0287 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0287_checked oddSum0287_checked hlen hs


end
end ErdosOverlap.Native6Grid
