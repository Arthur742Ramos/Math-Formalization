module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck042
public import ErdosOverlap.Certificate.Native6Grid.Coefficients05

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0336 :
    completeCoefficientRowCheck factorRow row0336 336 coefficients0336 = true := by
  have hlen : coefficients0336.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0336 oddDots0336
      641 336 0 coefficients0336 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0336_checked oddSum0336_checked hlen hs

theorem coefficientCheck0337 :
    completeCoefficientRowCheck factorRow row0337 337 coefficients0337 = true := by
  have hlen : coefficients0337.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0337 oddDots0337
      641 337 0 coefficients0337 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0337_checked oddSum0337_checked hlen hs

theorem coefficientCheck0338 :
    completeCoefficientRowCheck factorRow row0338 338 coefficients0338 = true := by
  have hlen : coefficients0338.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0338 oddDots0338
      641 338 0 coefficients0338 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0338_checked oddSum0338_checked hlen hs

theorem coefficientCheck0339 :
    completeCoefficientRowCheck factorRow row0339 339 coefficients0339 = true := by
  have hlen : coefficients0339.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0339 oddDots0339
      641 339 0 coefficients0339 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0339_checked oddSum0339_checked hlen hs

theorem coefficientCheck0340 :
    completeCoefficientRowCheck factorRow row0340 340 coefficients0340 = true := by
  have hlen : coefficients0340.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0340 oddDots0340
      641 340 0 coefficients0340 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0340_checked oddSum0340_checked hlen hs

theorem coefficientCheck0341 :
    completeCoefficientRowCheck factorRow row0341 341 coefficients0341 = true := by
  have hlen : coefficients0341.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0341 oddDots0341
      641 341 0 coefficients0341 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0341_checked oddSum0341_checked hlen hs

theorem coefficientCheck0342 :
    completeCoefficientRowCheck factorRow row0342 342 coefficients0342 = true := by
  have hlen : coefficients0342.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0342 oddDots0342
      641 342 0 coefficients0342 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0342_checked oddSum0342_checked hlen hs

theorem coefficientCheck0343 :
    completeCoefficientRowCheck factorRow row0343 343 coefficients0343 = true := by
  have hlen : coefficients0343.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0343 oddDots0343
      641 343 0 coefficients0343 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0343_checked oddSum0343_checked hlen hs


end
end ErdosOverlap.Native6Grid
