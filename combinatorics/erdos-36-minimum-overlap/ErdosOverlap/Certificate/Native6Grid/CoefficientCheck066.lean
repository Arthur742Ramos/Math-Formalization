module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck066
public import ErdosOverlap.Certificate.Native6Grid.Coefficients08

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0528 :
    completeCoefficientRowCheck factorRow row0528 528 coefficients0528 = true := by
  have hlen : coefficients0528.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0528 oddDots0528
      641 528 0 coefficients0528 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0528_checked oddSum0528_checked hlen hs

theorem coefficientCheck0529 :
    completeCoefficientRowCheck factorRow row0529 529 coefficients0529 = true := by
  have hlen : coefficients0529.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0529 oddDots0529
      641 529 0 coefficients0529 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0529_checked oddSum0529_checked hlen hs

theorem coefficientCheck0530 :
    completeCoefficientRowCheck factorRow row0530 530 coefficients0530 = true := by
  have hlen : coefficients0530.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0530 oddDots0530
      641 530 0 coefficients0530 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0530_checked oddSum0530_checked hlen hs

theorem coefficientCheck0531 :
    completeCoefficientRowCheck factorRow row0531 531 coefficients0531 = true := by
  have hlen : coefficients0531.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0531 oddDots0531
      641 531 0 coefficients0531 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0531_checked oddSum0531_checked hlen hs

theorem coefficientCheck0532 :
    completeCoefficientRowCheck factorRow row0532 532 coefficients0532 = true := by
  have hlen : coefficients0532.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0532 oddDots0532
      641 532 0 coefficients0532 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0532_checked oddSum0532_checked hlen hs

theorem coefficientCheck0533 :
    completeCoefficientRowCheck factorRow row0533 533 coefficients0533 = true := by
  have hlen : coefficients0533.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0533 oddDots0533
      641 533 0 coefficients0533 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0533_checked oddSum0533_checked hlen hs

theorem coefficientCheck0534 :
    completeCoefficientRowCheck factorRow row0534 534 coefficients0534 = true := by
  have hlen : coefficients0534.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0534 oddDots0534
      641 534 0 coefficients0534 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0534_checked oddSum0534_checked hlen hs

theorem coefficientCheck0535 :
    completeCoefficientRowCheck factorRow row0535 535 coefficients0535 = true := by
  have hlen : coefficients0535.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0535 oddDots0535
      641 535 0 coefficients0535 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0535_checked oddSum0535_checked hlen hs


end
end ErdosOverlap.Native6Grid
