module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck063
public import ErdosOverlap.Certificate.Native6Grid.Coefficients07

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0504 :
    completeCoefficientRowCheck factorRow row0504 504 coefficients0504 = true := by
  have hlen : coefficients0504.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0504 oddDots0504
      641 504 0 coefficients0504 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0504_checked oddSum0504_checked hlen hs

theorem coefficientCheck0505 :
    completeCoefficientRowCheck factorRow row0505 505 coefficients0505 = true := by
  have hlen : coefficients0505.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0505 oddDots0505
      641 505 0 coefficients0505 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0505_checked oddSum0505_checked hlen hs

theorem coefficientCheck0506 :
    completeCoefficientRowCheck factorRow row0506 506 coefficients0506 = true := by
  have hlen : coefficients0506.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0506 oddDots0506
      641 506 0 coefficients0506 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0506_checked oddSum0506_checked hlen hs

theorem coefficientCheck0507 :
    completeCoefficientRowCheck factorRow row0507 507 coefficients0507 = true := by
  have hlen : coefficients0507.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0507 oddDots0507
      641 507 0 coefficients0507 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0507_checked oddSum0507_checked hlen hs

theorem coefficientCheck0508 :
    completeCoefficientRowCheck factorRow row0508 508 coefficients0508 = true := by
  have hlen : coefficients0508.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0508 oddDots0508
      641 508 0 coefficients0508 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0508_checked oddSum0508_checked hlen hs

theorem coefficientCheck0509 :
    completeCoefficientRowCheck factorRow row0509 509 coefficients0509 = true := by
  have hlen : coefficients0509.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0509 oddDots0509
      641 509 0 coefficients0509 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0509_checked oddSum0509_checked hlen hs

theorem coefficientCheck0510 :
    completeCoefficientRowCheck factorRow row0510 510 coefficients0510 = true := by
  have hlen : coefficients0510.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0510 oddDots0510
      641 510 0 coefficients0510 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0510_checked oddSum0510_checked hlen hs

theorem coefficientCheck0511 :
    completeCoefficientRowCheck factorRow row0511 511 coefficients0511 = true := by
  have hlen : coefficients0511.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0511 oddDots0511
      641 511 0 coefficients0511 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0511_checked oddSum0511_checked hlen hs


end
end ErdosOverlap.Native6Grid
