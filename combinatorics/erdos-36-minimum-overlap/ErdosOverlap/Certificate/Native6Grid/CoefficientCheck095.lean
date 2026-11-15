module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck095
public import ErdosOverlap.Certificate.Native6Grid.Coefficients11

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0760 :
    completeCoefficientRowCheck factorRow row0760 760 coefficients0760 = true := by
  have hlen : coefficients0760.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0760 oddDots0760
      641 760 0 coefficients0760 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0760_checked oddSum0760_checked hlen hs

theorem coefficientCheck0761 :
    completeCoefficientRowCheck factorRow row0761 761 coefficients0761 = true := by
  have hlen : coefficients0761.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0761 oddDots0761
      641 761 0 coefficients0761 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0761_checked oddSum0761_checked hlen hs

theorem coefficientCheck0762 :
    completeCoefficientRowCheck factorRow row0762 762 coefficients0762 = true := by
  have hlen : coefficients0762.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0762 oddDots0762
      641 762 0 coefficients0762 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0762_checked oddSum0762_checked hlen hs

theorem coefficientCheck0763 :
    completeCoefficientRowCheck factorRow row0763 763 coefficients0763 = true := by
  have hlen : coefficients0763.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0763 oddDots0763
      641 763 0 coefficients0763 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0763_checked oddSum0763_checked hlen hs

theorem coefficientCheck0764 :
    completeCoefficientRowCheck factorRow row0764 764 coefficients0764 = true := by
  have hlen : coefficients0764.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0764 oddDots0764
      641 764 0 coefficients0764 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0764_checked oddSum0764_checked hlen hs

theorem coefficientCheck0765 :
    completeCoefficientRowCheck factorRow row0765 765 coefficients0765 = true := by
  have hlen : coefficients0765.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0765 oddDots0765
      641 765 0 coefficients0765 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0765_checked oddSum0765_checked hlen hs

theorem coefficientCheck0766 :
    completeCoefficientRowCheck factorRow row0766 766 coefficients0766 = true := by
  have hlen : coefficients0766.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0766 oddDots0766
      641 766 0 coefficients0766 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0766_checked oddSum0766_checked hlen hs

theorem coefficientCheck0767 :
    completeCoefficientRowCheck factorRow row0767 767 coefficients0767 = true := by
  have hlen : coefficients0767.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0767 oddDots0767
      641 767 0 coefficients0767 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0767_checked oddSum0767_checked hlen hs


end
end ErdosOverlap.Native6Grid
