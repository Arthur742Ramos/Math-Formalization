module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck046
public import ErdosOverlap.Certificate.Native6Grid.Coefficients05

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0368 :
    completeCoefficientRowCheck factorRow row0368 368 coefficients0368 = true := by
  have hlen : coefficients0368.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0368 oddDots0368
      641 368 0 coefficients0368 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0368_checked oddSum0368_checked hlen hs

theorem coefficientCheck0369 :
    completeCoefficientRowCheck factorRow row0369 369 coefficients0369 = true := by
  have hlen : coefficients0369.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0369 oddDots0369
      641 369 0 coefficients0369 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0369_checked oddSum0369_checked hlen hs

theorem coefficientCheck0370 :
    completeCoefficientRowCheck factorRow row0370 370 coefficients0370 = true := by
  have hlen : coefficients0370.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0370 oddDots0370
      641 370 0 coefficients0370 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0370_checked oddSum0370_checked hlen hs

theorem coefficientCheck0371 :
    completeCoefficientRowCheck factorRow row0371 371 coefficients0371 = true := by
  have hlen : coefficients0371.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0371 oddDots0371
      641 371 0 coefficients0371 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0371_checked oddSum0371_checked hlen hs

theorem coefficientCheck0372 :
    completeCoefficientRowCheck factorRow row0372 372 coefficients0372 = true := by
  have hlen : coefficients0372.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0372 oddDots0372
      641 372 0 coefficients0372 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0372_checked oddSum0372_checked hlen hs

theorem coefficientCheck0373 :
    completeCoefficientRowCheck factorRow row0373 373 coefficients0373 = true := by
  have hlen : coefficients0373.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0373 oddDots0373
      641 373 0 coefficients0373 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0373_checked oddSum0373_checked hlen hs

theorem coefficientCheck0374 :
    completeCoefficientRowCheck factorRow row0374 374 coefficients0374 = true := by
  have hlen : coefficients0374.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0374 oddDots0374
      641 374 0 coefficients0374 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0374_checked oddSum0374_checked hlen hs

theorem coefficientCheck0375 :
    completeCoefficientRowCheck factorRow row0375 375 coefficients0375 = true := by
  have hlen : coefficients0375.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0375 oddDots0375
      641 375 0 coefficients0375 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0375_checked oddSum0375_checked hlen hs


end
end ErdosOverlap.Native6Grid
