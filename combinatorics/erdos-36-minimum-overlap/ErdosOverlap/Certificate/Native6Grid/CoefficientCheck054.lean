module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck054
public import ErdosOverlap.Certificate.Native6Grid.Coefficients06

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0432 :
    completeCoefficientRowCheck factorRow row0432 432 coefficients0432 = true := by
  have hlen : coefficients0432.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0432 oddDots0432
      641 432 0 coefficients0432 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0432_checked oddSum0432_checked hlen hs

theorem coefficientCheck0433 :
    completeCoefficientRowCheck factorRow row0433 433 coefficients0433 = true := by
  have hlen : coefficients0433.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0433 oddDots0433
      641 433 0 coefficients0433 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0433_checked oddSum0433_checked hlen hs

theorem coefficientCheck0434 :
    completeCoefficientRowCheck factorRow row0434 434 coefficients0434 = true := by
  have hlen : coefficients0434.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0434 oddDots0434
      641 434 0 coefficients0434 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0434_checked oddSum0434_checked hlen hs

theorem coefficientCheck0435 :
    completeCoefficientRowCheck factorRow row0435 435 coefficients0435 = true := by
  have hlen : coefficients0435.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0435 oddDots0435
      641 435 0 coefficients0435 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0435_checked oddSum0435_checked hlen hs

theorem coefficientCheck0436 :
    completeCoefficientRowCheck factorRow row0436 436 coefficients0436 = true := by
  have hlen : coefficients0436.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0436 oddDots0436
      641 436 0 coefficients0436 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0436_checked oddSum0436_checked hlen hs

theorem coefficientCheck0437 :
    completeCoefficientRowCheck factorRow row0437 437 coefficients0437 = true := by
  have hlen : coefficients0437.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0437 oddDots0437
      641 437 0 coefficients0437 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0437_checked oddSum0437_checked hlen hs

theorem coefficientCheck0438 :
    completeCoefficientRowCheck factorRow row0438 438 coefficients0438 = true := by
  have hlen : coefficients0438.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0438 oddDots0438
      641 438 0 coefficients0438 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0438_checked oddSum0438_checked hlen hs

theorem coefficientCheck0439 :
    completeCoefficientRowCheck factorRow row0439 439 coefficients0439 = true := by
  have hlen : coefficients0439.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0439 oddDots0439
      641 439 0 coefficients0439 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0439_checked oddSum0439_checked hlen hs


end
end ErdosOverlap.Native6Grid
