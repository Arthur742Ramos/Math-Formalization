module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck057
public import ErdosOverlap.Certificate.Native6Grid.Coefficients07

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0456 :
    completeCoefficientRowCheck factorRow row0456 456 coefficients0456 = true := by
  have hlen : coefficients0456.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0456 oddDots0456
      641 456 0 coefficients0456 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0456_checked oddSum0456_checked hlen hs

theorem coefficientCheck0457 :
    completeCoefficientRowCheck factorRow row0457 457 coefficients0457 = true := by
  have hlen : coefficients0457.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0457 oddDots0457
      641 457 0 coefficients0457 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0457_checked oddSum0457_checked hlen hs

theorem coefficientCheck0458 :
    completeCoefficientRowCheck factorRow row0458 458 coefficients0458 = true := by
  have hlen : coefficients0458.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0458 oddDots0458
      641 458 0 coefficients0458 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0458_checked oddSum0458_checked hlen hs

theorem coefficientCheck0459 :
    completeCoefficientRowCheck factorRow row0459 459 coefficients0459 = true := by
  have hlen : coefficients0459.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0459 oddDots0459
      641 459 0 coefficients0459 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0459_checked oddSum0459_checked hlen hs

theorem coefficientCheck0460 :
    completeCoefficientRowCheck factorRow row0460 460 coefficients0460 = true := by
  have hlen : coefficients0460.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0460 oddDots0460
      641 460 0 coefficients0460 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0460_checked oddSum0460_checked hlen hs

theorem coefficientCheck0461 :
    completeCoefficientRowCheck factorRow row0461 461 coefficients0461 = true := by
  have hlen : coefficients0461.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0461 oddDots0461
      641 461 0 coefficients0461 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0461_checked oddSum0461_checked hlen hs

theorem coefficientCheck0462 :
    completeCoefficientRowCheck factorRow row0462 462 coefficients0462 = true := by
  have hlen : coefficients0462.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0462 oddDots0462
      641 462 0 coefficients0462 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0462_checked oddSum0462_checked hlen hs

theorem coefficientCheck0463 :
    completeCoefficientRowCheck factorRow row0463 463 coefficients0463 = true := by
  have hlen : coefficients0463.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0463 oddDots0463
      641 463 0 coefficients0463 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0463_checked oddSum0463_checked hlen hs


end
end ErdosOverlap.Native6Grid
