module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck091
public import ErdosOverlap.Certificate.Native6Grid.Coefficients11

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0728 :
    completeCoefficientRowCheck factorRow row0728 728 coefficients0728 = true := by
  have hlen : coefficients0728.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0728 oddDots0728
      641 728 0 coefficients0728 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0728_checked oddSum0728_checked hlen hs

theorem coefficientCheck0729 :
    completeCoefficientRowCheck factorRow row0729 729 coefficients0729 = true := by
  have hlen : coefficients0729.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0729 oddDots0729
      641 729 0 coefficients0729 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0729_checked oddSum0729_checked hlen hs

theorem coefficientCheck0730 :
    completeCoefficientRowCheck factorRow row0730 730 coefficients0730 = true := by
  have hlen : coefficients0730.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0730 oddDots0730
      641 730 0 coefficients0730 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0730_checked oddSum0730_checked hlen hs

theorem coefficientCheck0731 :
    completeCoefficientRowCheck factorRow row0731 731 coefficients0731 = true := by
  have hlen : coefficients0731.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0731 oddDots0731
      641 731 0 coefficients0731 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0731_checked oddSum0731_checked hlen hs

theorem coefficientCheck0732 :
    completeCoefficientRowCheck factorRow row0732 732 coefficients0732 = true := by
  have hlen : coefficients0732.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0732 oddDots0732
      641 732 0 coefficients0732 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0732_checked oddSum0732_checked hlen hs

theorem coefficientCheck0733 :
    completeCoefficientRowCheck factorRow row0733 733 coefficients0733 = true := by
  have hlen : coefficients0733.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0733 oddDots0733
      641 733 0 coefficients0733 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0733_checked oddSum0733_checked hlen hs

theorem coefficientCheck0734 :
    completeCoefficientRowCheck factorRow row0734 734 coefficients0734 = true := by
  have hlen : coefficients0734.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0734 oddDots0734
      641 734 0 coefficients0734 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0734_checked oddSum0734_checked hlen hs

theorem coefficientCheck0735 :
    completeCoefficientRowCheck factorRow row0735 735 coefficients0735 = true := by
  have hlen : coefficients0735.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0735 oddDots0735
      641 735 0 coefficients0735 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0735_checked oddSum0735_checked hlen hs


end
end ErdosOverlap.Native6Grid
