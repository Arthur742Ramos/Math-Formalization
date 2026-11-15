module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck044
public import ErdosOverlap.Certificate.Native6Grid.Coefficients05

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0352 :
    completeCoefficientRowCheck factorRow row0352 352 coefficients0352 = true := by
  have hlen : coefficients0352.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0352 oddDots0352
      641 352 0 coefficients0352 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0352_checked oddSum0352_checked hlen hs

theorem coefficientCheck0353 :
    completeCoefficientRowCheck factorRow row0353 353 coefficients0353 = true := by
  have hlen : coefficients0353.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0353 oddDots0353
      641 353 0 coefficients0353 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0353_checked oddSum0353_checked hlen hs

theorem coefficientCheck0354 :
    completeCoefficientRowCheck factorRow row0354 354 coefficients0354 = true := by
  have hlen : coefficients0354.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0354 oddDots0354
      641 354 0 coefficients0354 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0354_checked oddSum0354_checked hlen hs

theorem coefficientCheck0355 :
    completeCoefficientRowCheck factorRow row0355 355 coefficients0355 = true := by
  have hlen : coefficients0355.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0355 oddDots0355
      641 355 0 coefficients0355 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0355_checked oddSum0355_checked hlen hs

theorem coefficientCheck0356 :
    completeCoefficientRowCheck factorRow row0356 356 coefficients0356 = true := by
  have hlen : coefficients0356.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0356 oddDots0356
      641 356 0 coefficients0356 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0356_checked oddSum0356_checked hlen hs

theorem coefficientCheck0357 :
    completeCoefficientRowCheck factorRow row0357 357 coefficients0357 = true := by
  have hlen : coefficients0357.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0357 oddDots0357
      641 357 0 coefficients0357 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0357_checked oddSum0357_checked hlen hs

theorem coefficientCheck0358 :
    completeCoefficientRowCheck factorRow row0358 358 coefficients0358 = true := by
  have hlen : coefficients0358.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0358 oddDots0358
      641 358 0 coefficients0358 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0358_checked oddSum0358_checked hlen hs

theorem coefficientCheck0359 :
    completeCoefficientRowCheck factorRow row0359 359 coefficients0359 = true := by
  have hlen : coefficients0359.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0359 oddDots0359
      641 359 0 coefficients0359 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0359_checked oddSum0359_checked hlen hs


end
end ErdosOverlap.Native6Grid
