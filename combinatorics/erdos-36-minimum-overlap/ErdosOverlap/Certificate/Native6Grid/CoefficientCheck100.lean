module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck100
public import ErdosOverlap.Certificate.Native6Grid.Coefficients12

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0800 :
    completeCoefficientRowCheck factorRow row0800 800 coefficients0800 = true := by
  have hlen : coefficients0800.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0800 oddDots0800
      641 800 0 coefficients0800 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0800_checked oddSum0800_checked hlen hs

theorem coefficientCheck0801 :
    completeCoefficientRowCheck factorRow row0801 801 coefficients0801 = true := by
  have hlen : coefficients0801.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0801 oddDots0801
      641 801 0 coefficients0801 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0801_checked oddSum0801_checked hlen hs

theorem coefficientCheck0802 :
    completeCoefficientRowCheck factorRow row0802 802 coefficients0802 = true := by
  have hlen : coefficients0802.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0802 oddDots0802
      641 802 0 coefficients0802 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0802_checked oddSum0802_checked hlen hs

theorem coefficientCheck0803 :
    completeCoefficientRowCheck factorRow row0803 803 coefficients0803 = true := by
  have hlen : coefficients0803.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0803 oddDots0803
      641 803 0 coefficients0803 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0803_checked oddSum0803_checked hlen hs

theorem coefficientCheck0804 :
    completeCoefficientRowCheck factorRow row0804 804 coefficients0804 = true := by
  have hlen : coefficients0804.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0804 oddDots0804
      641 804 0 coefficients0804 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0804_checked oddSum0804_checked hlen hs

theorem coefficientCheck0805 :
    completeCoefficientRowCheck factorRow row0805 805 coefficients0805 = true := by
  have hlen : coefficients0805.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0805 oddDots0805
      641 805 0 coefficients0805 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0805_checked oddSum0805_checked hlen hs

theorem coefficientCheck0806 :
    completeCoefficientRowCheck factorRow row0806 806 coefficients0806 = true := by
  have hlen : coefficients0806.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0806 oddDots0806
      641 806 0 coefficients0806 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0806_checked oddSum0806_checked hlen hs

theorem coefficientCheck0807 :
    completeCoefficientRowCheck factorRow row0807 807 coefficients0807 = true := by
  have hlen : coefficients0807.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0807 oddDots0807
      641 807 0 coefficients0807 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0807_checked oddSum0807_checked hlen hs


end
end ErdosOverlap.Native6Grid
