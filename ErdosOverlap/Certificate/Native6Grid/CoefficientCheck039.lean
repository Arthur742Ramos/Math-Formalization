module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck039
public import ErdosOverlap.Certificate.Native6Grid.Coefficients04

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0312 :
    completeCoefficientRowCheck factorRow row0312 312 coefficients0312 = true := by
  have hlen : coefficients0312.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0312 oddDots0312
      641 312 0 coefficients0312 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0312_checked oddSum0312_checked hlen hs

theorem coefficientCheck0313 :
    completeCoefficientRowCheck factorRow row0313 313 coefficients0313 = true := by
  have hlen : coefficients0313.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0313 oddDots0313
      641 313 0 coefficients0313 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0313_checked oddSum0313_checked hlen hs

theorem coefficientCheck0314 :
    completeCoefficientRowCheck factorRow row0314 314 coefficients0314 = true := by
  have hlen : coefficients0314.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0314 oddDots0314
      641 314 0 coefficients0314 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0314_checked oddSum0314_checked hlen hs

theorem coefficientCheck0315 :
    completeCoefficientRowCheck factorRow row0315 315 coefficients0315 = true := by
  have hlen : coefficients0315.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0315 oddDots0315
      641 315 0 coefficients0315 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0315_checked oddSum0315_checked hlen hs

theorem coefficientCheck0316 :
    completeCoefficientRowCheck factorRow row0316 316 coefficients0316 = true := by
  have hlen : coefficients0316.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0316 oddDots0316
      641 316 0 coefficients0316 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0316_checked oddSum0316_checked hlen hs

theorem coefficientCheck0317 :
    completeCoefficientRowCheck factorRow row0317 317 coefficients0317 = true := by
  have hlen : coefficients0317.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0317 oddDots0317
      641 317 0 coefficients0317 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0317_checked oddSum0317_checked hlen hs

theorem coefficientCheck0318 :
    completeCoefficientRowCheck factorRow row0318 318 coefficients0318 = true := by
  have hlen : coefficients0318.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0318 oddDots0318
      641 318 0 coefficients0318 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0318_checked oddSum0318_checked hlen hs

theorem coefficientCheck0319 :
    completeCoefficientRowCheck factorRow row0319 319 coefficients0319 = true := by
  have hlen : coefficients0319.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0319 oddDots0319
      641 319 0 coefficients0319 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0319_checked oddSum0319_checked hlen hs


end
end ErdosOverlap.Native6Grid
