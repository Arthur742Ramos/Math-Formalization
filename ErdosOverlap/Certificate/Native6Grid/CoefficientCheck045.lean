module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck045
public import ErdosOverlap.Certificate.Native6Grid.Coefficients05

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0360 :
    completeCoefficientRowCheck factorRow row0360 360 coefficients0360 = true := by
  have hlen : coefficients0360.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0360 oddDots0360
      641 360 0 coefficients0360 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0360_checked oddSum0360_checked hlen hs

theorem coefficientCheck0361 :
    completeCoefficientRowCheck factorRow row0361 361 coefficients0361 = true := by
  have hlen : coefficients0361.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0361 oddDots0361
      641 361 0 coefficients0361 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0361_checked oddSum0361_checked hlen hs

theorem coefficientCheck0362 :
    completeCoefficientRowCheck factorRow row0362 362 coefficients0362 = true := by
  have hlen : coefficients0362.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0362 oddDots0362
      641 362 0 coefficients0362 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0362_checked oddSum0362_checked hlen hs

theorem coefficientCheck0363 :
    completeCoefficientRowCheck factorRow row0363 363 coefficients0363 = true := by
  have hlen : coefficients0363.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0363 oddDots0363
      641 363 0 coefficients0363 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0363_checked oddSum0363_checked hlen hs

theorem coefficientCheck0364 :
    completeCoefficientRowCheck factorRow row0364 364 coefficients0364 = true := by
  have hlen : coefficients0364.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0364 oddDots0364
      641 364 0 coefficients0364 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0364_checked oddSum0364_checked hlen hs

theorem coefficientCheck0365 :
    completeCoefficientRowCheck factorRow row0365 365 coefficients0365 = true := by
  have hlen : coefficients0365.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0365 oddDots0365
      641 365 0 coefficients0365 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0365_checked oddSum0365_checked hlen hs

theorem coefficientCheck0366 :
    completeCoefficientRowCheck factorRow row0366 366 coefficients0366 = true := by
  have hlen : coefficients0366.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0366 oddDots0366
      641 366 0 coefficients0366 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0366_checked oddSum0366_checked hlen hs

theorem coefficientCheck0367 :
    completeCoefficientRowCheck factorRow row0367 367 coefficients0367 = true := by
  have hlen : coefficients0367.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0367 oddDots0367
      641 367 0 coefficients0367 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0367_checked oddSum0367_checked hlen hs


end
end ErdosOverlap.Native6Grid
