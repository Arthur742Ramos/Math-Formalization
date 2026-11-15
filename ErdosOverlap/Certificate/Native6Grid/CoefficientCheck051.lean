module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck051
public import ErdosOverlap.Certificate.Native6Grid.Coefficients06

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0408 :
    completeCoefficientRowCheck factorRow row0408 408 coefficients0408 = true := by
  have hlen : coefficients0408.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0408 oddDots0408
      641 408 0 coefficients0408 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0408_checked oddSum0408_checked hlen hs

theorem coefficientCheck0409 :
    completeCoefficientRowCheck factorRow row0409 409 coefficients0409 = true := by
  have hlen : coefficients0409.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0409 oddDots0409
      641 409 0 coefficients0409 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0409_checked oddSum0409_checked hlen hs

theorem coefficientCheck0410 :
    completeCoefficientRowCheck factorRow row0410 410 coefficients0410 = true := by
  have hlen : coefficients0410.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0410 oddDots0410
      641 410 0 coefficients0410 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0410_checked oddSum0410_checked hlen hs

theorem coefficientCheck0411 :
    completeCoefficientRowCheck factorRow row0411 411 coefficients0411 = true := by
  have hlen : coefficients0411.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0411 oddDots0411
      641 411 0 coefficients0411 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0411_checked oddSum0411_checked hlen hs

theorem coefficientCheck0412 :
    completeCoefficientRowCheck factorRow row0412 412 coefficients0412 = true := by
  have hlen : coefficients0412.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0412 oddDots0412
      641 412 0 coefficients0412 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0412_checked oddSum0412_checked hlen hs

theorem coefficientCheck0413 :
    completeCoefficientRowCheck factorRow row0413 413 coefficients0413 = true := by
  have hlen : coefficients0413.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0413 oddDots0413
      641 413 0 coefficients0413 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0413_checked oddSum0413_checked hlen hs

theorem coefficientCheck0414 :
    completeCoefficientRowCheck factorRow row0414 414 coefficients0414 = true := by
  have hlen : coefficients0414.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0414 oddDots0414
      641 414 0 coefficients0414 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0414_checked oddSum0414_checked hlen hs

theorem coefficientCheck0415 :
    completeCoefficientRowCheck factorRow row0415 415 coefficients0415 = true := by
  have hlen : coefficients0415.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0415 oddDots0415
      641 415 0 coefficients0415 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0415_checked oddSum0415_checked hlen hs


end
end ErdosOverlap.Native6Grid
