module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck075
public import ErdosOverlap.Certificate.Native6Grid.Coefficients09

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0600 :
    completeCoefficientRowCheck factorRow row0600 600 coefficients0600 = true := by
  have hlen : coefficients0600.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0600 oddDots0600
      641 600 0 coefficients0600 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0600_checked oddSum0600_checked hlen hs

theorem coefficientCheck0601 :
    completeCoefficientRowCheck factorRow row0601 601 coefficients0601 = true := by
  have hlen : coefficients0601.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0601 oddDots0601
      641 601 0 coefficients0601 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0601_checked oddSum0601_checked hlen hs

theorem coefficientCheck0602 :
    completeCoefficientRowCheck factorRow row0602 602 coefficients0602 = true := by
  have hlen : coefficients0602.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0602 oddDots0602
      641 602 0 coefficients0602 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0602_checked oddSum0602_checked hlen hs

theorem coefficientCheck0603 :
    completeCoefficientRowCheck factorRow row0603 603 coefficients0603 = true := by
  have hlen : coefficients0603.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0603 oddDots0603
      641 603 0 coefficients0603 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0603_checked oddSum0603_checked hlen hs

theorem coefficientCheck0604 :
    completeCoefficientRowCheck factorRow row0604 604 coefficients0604 = true := by
  have hlen : coefficients0604.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0604 oddDots0604
      641 604 0 coefficients0604 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0604_checked oddSum0604_checked hlen hs

theorem coefficientCheck0605 :
    completeCoefficientRowCheck factorRow row0605 605 coefficients0605 = true := by
  have hlen : coefficients0605.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0605 oddDots0605
      641 605 0 coefficients0605 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0605_checked oddSum0605_checked hlen hs

theorem coefficientCheck0606 :
    completeCoefficientRowCheck factorRow row0606 606 coefficients0606 = true := by
  have hlen : coefficients0606.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0606 oddDots0606
      641 606 0 coefficients0606 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0606_checked oddSum0606_checked hlen hs

theorem coefficientCheck0607 :
    completeCoefficientRowCheck factorRow row0607 607 coefficients0607 = true := by
  have hlen : coefficients0607.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0607 oddDots0607
      641 607 0 coefficients0607 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0607_checked oddSum0607_checked hlen hs


end
end ErdosOverlap.Native6Grid
