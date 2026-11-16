module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck056
public import ErdosOverlap.Certificate.Native6Grid.Coefficients07

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0448 :
    completeCoefficientRowCheck factorRow row0448 448 coefficients0448 = true := by
  have hlen : coefficients0448.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0448 oddDots0448
      641 448 0 coefficients0448 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0448_checked oddSum0448_checked hlen hs

theorem coefficientCheck0449 :
    completeCoefficientRowCheck factorRow row0449 449 coefficients0449 = true := by
  have hlen : coefficients0449.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0449 oddDots0449
      641 449 0 coefficients0449 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0449_checked oddSum0449_checked hlen hs

theorem coefficientCheck0450 :
    completeCoefficientRowCheck factorRow row0450 450 coefficients0450 = true := by
  have hlen : coefficients0450.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0450 oddDots0450
      641 450 0 coefficients0450 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0450_checked oddSum0450_checked hlen hs

theorem coefficientCheck0451 :
    completeCoefficientRowCheck factorRow row0451 451 coefficients0451 = true := by
  have hlen : coefficients0451.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0451 oddDots0451
      641 451 0 coefficients0451 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0451_checked oddSum0451_checked hlen hs

theorem coefficientCheck0452 :
    completeCoefficientRowCheck factorRow row0452 452 coefficients0452 = true := by
  have hlen : coefficients0452.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0452 oddDots0452
      641 452 0 coefficients0452 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0452_checked oddSum0452_checked hlen hs

theorem coefficientCheck0453 :
    completeCoefficientRowCheck factorRow row0453 453 coefficients0453 = true := by
  have hlen : coefficients0453.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0453 oddDots0453
      641 453 0 coefficients0453 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0453_checked oddSum0453_checked hlen hs

theorem coefficientCheck0454 :
    completeCoefficientRowCheck factorRow row0454 454 coefficients0454 = true := by
  have hlen : coefficients0454.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0454 oddDots0454
      641 454 0 coefficients0454 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0454_checked oddSum0454_checked hlen hs

theorem coefficientCheck0455 :
    completeCoefficientRowCheck factorRow row0455 455 coefficients0455 = true := by
  have hlen : coefficients0455.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0455 oddDots0455
      641 455 0 coefficients0455 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0455_checked oddSum0455_checked hlen hs


end
end ErdosOverlap.Native6Grid
