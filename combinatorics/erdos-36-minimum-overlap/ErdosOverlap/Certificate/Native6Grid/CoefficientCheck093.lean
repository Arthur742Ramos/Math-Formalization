module

public import ErdosOverlap.Numerics.PackedTaylor
public import ErdosOverlap.Certificate.Native6Grid.FactorPacking
public import ErdosOverlap.Certificate.Native6Grid.PackedSumCheck093
public import ErdosOverlap.Certificate.Native6Grid.Coefficients11

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem coefficientCheck0744 :
    completeCoefficientRowCheck factorRow row0744 744 coefficients0744 = true := by
  have hlen : coefficients0744.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0744 oddDots0744
      641 744 0 coefficients0744 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0744_checked oddSum0744_checked hlen hs

theorem coefficientCheck0745 :
    completeCoefficientRowCheck factorRow row0745 745 coefficients0745 = true := by
  have hlen : coefficients0745.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0745 oddDots0745
      641 745 0 coefficients0745 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0745_checked oddSum0745_checked hlen hs

theorem coefficientCheck0746 :
    completeCoefficientRowCheck factorRow row0746 746 coefficients0746 = true := by
  have hlen : coefficients0746.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0746 oddDots0746
      641 746 0 coefficients0746 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0746_checked oddSum0746_checked hlen hs

theorem coefficientCheck0747 :
    completeCoefficientRowCheck factorRow row0747 747 coefficients0747 = true := by
  have hlen : coefficients0747.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0747 oddDots0747
      641 747 0 coefficients0747 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0747_checked oddSum0747_checked hlen hs

theorem coefficientCheck0748 :
    completeCoefficientRowCheck factorRow row0748 748 coefficients0748 = true := by
  have hlen : coefficients0748.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0748 oddDots0748
      641 748 0 coefficients0748 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0748_checked oddSum0748_checked hlen hs

theorem coefficientCheck0749 :
    completeCoefficientRowCheck factorRow row0749 749 coefficients0749 = true := by
  have hlen : coefficients0749.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0749 oddDots0749
      641 749 0 coefficients0749 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0749_checked oddSum0749_checked hlen hs

theorem coefficientCheck0750 :
    completeCoefficientRowCheck factorRow row0750 750 coefficients0750 = true := by
  have hlen : coefficients0750.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0750 oddDots0750
      641 750 0 coefficients0750 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0750_checked oddSum0750_checked hlen hs

theorem coefficientCheck0751 :
    completeCoefficientRowCheck factorRow row0751 751 coefficients0751 = true := by
  have hlen : coefficients0751.length = 20 := by decide +kernel
  have hs : storedScalarListCheck factorMass evenDots0751 oddDots0751
      641 751 0 coefficients0751 = true := by decide +kernel
  exact completeCoefficientRowCheck_of_packed evenFactors_packed oddFactors_packed
    factorMass_correct evenSum0751_checked oddSum0751_checked hlen hs


end
end ErdosOverlap.Native6Grid
