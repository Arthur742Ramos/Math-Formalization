module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck052
public import ErdosOverlap.Certificate.Native6Grid.Coefficients06

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0416 :
    completeCoefficientRowCheck factorRow row0416 416 coefficients0416 = true := by
  have hlen : coefficients0416.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0416 oddDots0416
      641 416 0 coefficients0416 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0416_checked oddSum0416_checked hlen hs

theorem coefficientCheck0417 :
    completeCoefficientRowCheck factorRow row0417 417 coefficients0417 = true := by
  have hlen : coefficients0417.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0417 oddDots0417
      641 417 0 coefficients0417 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0417_checked oddSum0417_checked hlen hs

theorem coefficientCheck0418 :
    completeCoefficientRowCheck factorRow row0418 418 coefficients0418 = true := by
  have hlen : coefficients0418.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0418 oddDots0418
      641 418 0 coefficients0418 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0418_checked oddSum0418_checked hlen hs

theorem coefficientCheck0419 :
    completeCoefficientRowCheck factorRow row0419 419 coefficients0419 = true := by
  have hlen : coefficients0419.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0419 oddDots0419
      641 419 0 coefficients0419 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0419_checked oddSum0419_checked hlen hs

theorem coefficientCheck0420 :
    completeCoefficientRowCheck factorRow row0420 420 coefficients0420 = true := by
  have hlen : coefficients0420.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0420 oddDots0420
      641 420 0 coefficients0420 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0420_checked oddSum0420_checked hlen hs

theorem coefficientCheck0421 :
    completeCoefficientRowCheck factorRow row0421 421 coefficients0421 = true := by
  have hlen : coefficients0421.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0421 oddDots0421
      641 421 0 coefficients0421 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0421_checked oddSum0421_checked hlen hs

theorem coefficientCheck0422 :
    completeCoefficientRowCheck factorRow row0422 422 coefficients0422 = true := by
  have hlen : coefficients0422.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0422 oddDots0422
      641 422 0 coefficients0422 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0422_checked oddSum0422_checked hlen hs

theorem coefficientCheck0423 :
    completeCoefficientRowCheck factorRow row0423 423 coefficients0423 = true := by
  have hlen : coefficients0423.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0423 oddDots0423
      641 423 0 coefficients0423 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0423_checked oddSum0423_checked hlen hs


end
end ErdosOverlap.Native6Grid
